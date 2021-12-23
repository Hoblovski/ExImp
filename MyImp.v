Require Import Frap TransitionSystems.
Require Import List Lia.

(* All variables are by default initialized to 0 *)
Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).

Section IMPLang.
  Notation Value := nat.

  Inductive BinopKind :=
  | Plus
  | Minus
  | Mul
  | Eq
  | Le
  | Land
  | Lor.

  Inductive UnaopKind :=
  | Lnot.

  Inductive Exp :=
  | Const (n : Value)
  | Var (x : var)
  | Unaop (op : UnaopKind) (e : Exp)
  | Binop (op : BinopKind) (e1 e2 : Exp).

  (* None means unitialized *)
  Definition valuation := fmap var Value.

  Definition hassertion := valuation -> Prop.

  Definition tauto_hassertion := fun (va : valuation) => True.
  Definition contra_hassertion := fun (va : valuation) => False.

  Inductive Cmd :=
  | Skip
  | Assign (x : var) (e : Exp)
  | Seq (c1 c2 : Cmd)
  | If (be : Exp) (th el : Cmd)
  | While (inv : hassertion) (be : Exp) (body : Cmd)
  | Assert (a : hassertion)
  | Assume (a : hassertion).

  Definition to_bool {A B} (s : sumbool A B) := if s then true else false.

  Definition nat_to_bool (n : nat) := negb (n =? 0)%nat.
  Definition bool_to_nat (b : bool) := if b then 1 else 0.

  Definition interp_unaopkind (k : UnaopKind) : Value -> Value :=
    match k with
     | Lnot => fun x => bool_to_nat (negb (nat_to_bool x))
    end.

  Definition interp_binopkind (k : BinopKind) : Value -> Value -> Value :=
    match k with
     | Plus => fun x y => x + y
     | Minus => fun x y => x - y
     | Mul => fun x y => x * y
     | Eq => fun x y => bool_to_nat (x =? y)
     | Le => fun x y => bool_to_nat (x <=? y)
     | Land => fun x y => bool_to_nat (nat_to_bool x && nat_to_bool y)
     | Lor => fun x y => bool_to_nat (nat_to_bool x || nat_to_bool y)
    end%nat.

  Fixpoint eval_exp (va : valuation) (e : Exp) : Value :=
    match e with
    | Const n => n
    | Var x => va $! x
    | Unaop op e =>
      let opv := (interp_unaopkind op) in
      let ev := eval_exp va e in
      opv ev
    | Binop op e1 e2 =>
      let opv := (interp_binopkind op) in
      let e1v := eval_exp va e1 in
      let e2v := eval_exp va e2 in
      opv e1v e2v
    end.
End IMPLang.

Section Big_step.
  (* relational big step *)
  Inductive eval : valuation -> Cmd -> valuation -> Prop :=
  | EvalDefault_Skip: forall va,
    eval va Skip va
  | EvalDefault_Assign: forall va x e ve,
    eval_exp va e = ve ->
    eval va (Assign x e) (va $+ (x, ve))
  | EvalDefault_Seq: forall va0 va1 va2 c0 c1,
    eval va0 c0 va1 ->
    eval va1 c1 va2 ->
    eval va0 (Seq c0 c1) va2
  | EvalDefault_If: forall va0 va1 be bev th el,
    eval_exp va0 be = bev ->
    eval va0 (if (nat_to_bool bev) then th else el) va1 ->
    eval va0 (If be th el) va1
  | EvalDefault_While0: forall va0 inv be bev body,
    eval_exp va0 be = bev ->
    nat_to_bool bev = false ->
    eval va0 (While inv be body) va0
  | EvalDefault_While1: forall va0 va1 va2 inv be bev body,
    eval_exp va0 be = bev ->
    nat_to_bool bev = true ->
    eval va0 body va1 ->
    eval va1 (While inv be body) va2 ->
    eval va0 (While inv be body) va2
  | EvalDefault_Assert: forall va0 (a : hassertion),
    a va0 ->
    eval va0 (Assert a) va0
  (* Assume behave like no-ops *)
  | EvalDefault_Assume: forall va0 a,
    eval va0 (Assume a) va0.
  Check tauto_hassertion.

  Example bigstep_ex0_code' :=
    (Seq
      (Assign "n" (Const 2))
      (While tauto_hassertion (Unaop Lnot (Binop Eq (Const 0) (Var "n")))
        (Seq
          (Assign "x" (Binop Plus (Var "x") (Const 2)))
          (Assign "n" (Binop Minus (Var "n") (Const 1)))))).

  Coercion Const : nat >-> Exp.
  Coercion Var : string >-> Exp.

  Example ex0_code :=
    (Seq
      (Assign "n" 2)
      (While tauto_hassertion (Unaop Lnot (Binop Eq 0 "n"))
        (Seq
          (Assign "x" (Binop Plus "x" 2))
          (Assign "n" (Binop Minus "n" 1))))).

  Example bigstep_ex0: forall va va', eval va ex0_code va' ->
    va' $! "n" = 0 /\ va' $! "x" = va $! "x" + 4.
  Proof.

  Ltac bs_simple :=
    simplify; repeat (match goal with
    | [ H: eval _ (Assign _ _) _ |- _ ] => invert H
    | [ H: eval _ (Seq _ _) _ |- _ ] => invert H
    end; simplify).

  Ltac bs_while :=
    simplify; match goal with
    | [ H: eval _ (While _ _ _) _ |- _ ] => invert H
    end; simplify;
    match goal with
    | [ H : nat_to_bool _ = _ |- _ ] => try invert H
    end.

    unfold ex0_code; simplify.
    bs_simple.
    bs_while.
    bs_simple.
    bs_while.
    bs_simple.
    bs_while.

    lia.
  Qed.

End Big_step.

Section Small_step.
  Definition step_state := (valuation * Cmd)%type.

  Inductive step : step_state -> step_state -> Prop :=
  | Step_Assign: forall va x e ve,
    eval_exp va e = ve ->
    step (va, (Assign x e)) (va $+ (x, ve), Skip)
  | Step_Seq0: forall va va' c0 c0' c1,
    step (va, c0) (va', c0') ->
    step (va, (Seq c0 c1)) (va', (Seq c0' c1))
  | Step_Seq1: forall va c1,
    step (va, (Seq Skip c1)) (va, c1)
  | Step_If: forall va be bev th el,
    eval_exp va be = bev ->
    step (va, (If be th el)) (va, if nat_to_bool bev then th else el)
  | Step_While1: forall va be inv body,
    nat_to_bool (eval_exp va be) = true ->
    step (va, (While inv be body)) (va, Seq body (While inv be body))
  | Step_While0: forall va be inv body,
    nat_to_bool (eval_exp va be) = false ->
    step (va, (While inv be body)) (va, Skip)
  | Step_Assert: forall va (a : hassertion),
    a va ->
    step (va, (Assert a)) (va, Skip)
  | Step_Assume: forall va (a : hassertion),
    step (va, (Assume a)) (va, Skip).

  Definition same_step_state (vac : step_state) (vac' : step_state) :=
  match vac, vac' with
  | (va, cmd), (va', cmd') => va = va' /\ cmd = cmd'
  end.

  Definition step_trsys_with_init (va : valuation) (code : Cmd) : trsys step_state := {|
    Initial := same_step_state (va, code);
    Step := step;
  |}.

  Definition term_step_state (vac : step_state) :=
  match vac with
  | (va, cmd) => cmd = Skip
  end.

  Example smallstep_ex0: forall va0 va1,
    reachable (step_trsys_with_init va0 ex0_code) (va1, Skip) ->
    va1 $! "x" = va0 $! "x" + 4.
  Proof.
    unfold ex0_code.
    simplify.

    invert H.
    simplify. destruct st0. invert H0.
    (* up are initial *)

    invert H1. destruct y.
    invert H. invert H2.
    invert H0. destruct y.

    invert H.
    invert H2.
    invert H1. invert H.
    - simplify. clear H6.
      invert H0. destruct y.
      invert H. invert H1. destruct y.
      invert H2. invert H3. invert H.
      invert H2. invert H1.
      invert H0. invert H. invert H5.
      invert H1. simplify.
      invert H. invert H5.
      invert H0. invert H.
      + simplify.  clear H6.
        invert H1. invert H. invert H5. invert H1.
        invert H0. invert H. simplify.
        invert H5. invert H0.
        invert H1. invert H. invert H5. invert H0.
        invert H. simplify. invert H5.
        invert H1. invert H.
        * simplify. invert H6.
        * simplify. clear H6.
          invert H0.
          { simplify. lia. }
          { invert H. }
      + simplify. invert H6.
    - simplify. invert H6.
  Restart.

  Ltac step_invert_one :=
    repeat match goal with
    | [ H : step _ _ |- _ ] => invert H
    end; simplify.

  Ltac step_one :=
    match goal with
    | [ H : step^* _ _ |- _ ] => invert H
    end;
    repeat step_invert_one;
    simplify.

  Ltac step_while :=
    step_one;
    match goal with
    | [ H : nat_to_bool _ = _ |- _ ] => try invert H
    end.

    unfold ex0_code; simplify.

    invert H.
    simplify. destruct st0. invert H0.
    (* Above: get the initial state *)

    step_one.
    step_one.
    step_while.
    step_one.
    step_one.
    step_one.
    step_one.
    step_while.
    step_one.
    step_one.
    step_one.
    step_one.
    step_while.

    invert H0.
    simplify. lia.
    invert H.
  Qed.

  Lemma equiv0_seq: forall va c1 c1' c2 va',
    step^* (va, c1) (va', c1') ->
    step^* (va, Seq c1 c2) (va', Seq c1' c2).
  Proof.
  (* The key to coq thinking is inducting on proofs *)
    induct 1.
    + constructor.
    + cases y.
      econstructor.
      constructor. eassumption.
      apply IHtrc; auto.
  Qed.

  Theorem equiv_big_small: forall code va va',
    eval va code va' -> step ^* (va, code) (va', Skip).
  Proof with (try econstructor; eauto).
    induct 1; simplify.
    + econstructor.
    + econstructor...
    + eapply trc_trans. apply equiv0_seq. eauto.
      econstructor. apply Step_Seq1. assumption.
    + econstructor. econstructor. eauto. assumption.
    + econstructor. apply Step_While0... constructor.
    + econstructor. apply Step_While1. equality.
      eapply trc_trans. apply equiv0_seq. eauto.
      econstructor. apply Step_Seq1. assumption.
    + econstructor...
    + econstructor...
  Qed.

(* CONFUSED: where does these all JMeq come from? *)

  Lemma equiv_small_big_one: forall code code' va va',
    step (va, code) (va', code') ->
    forall va'', eval va' code' va'' ->
      eval va code va''.
  Proof with (try econstructor; eauto).
    induct 1; simplify.
    + invert H...
    + invert H0. apply IHstep in H4...
    + econstructor...
    + idtac...
    + invert H0...
    + invert H0...
    + invert H0...
    + invert H...
  Qed.

  Theorem equiv_small_big: forall code va va',
    step^* (va, code) (va', Skip) -> eval va code va'.
  Proof.
    induct 1; simplify.
    econstructor.

    cases y.
    eapply equiv_small_big_one.
    eassumption.
    eapply IHtrc; auto.
  Qed.
End Small_step.

Section Unused.

  (* example: how to do fmap normalization *)
  assert ((va $+ ("n", 2) $+ ("x", va $! "x" + 2) $+ ("n", 1)) = (va $+ ("n", 1) $+ ("x", va $! "x" + 2)))
  by maps_equal.
End Unused.
