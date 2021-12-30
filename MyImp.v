Require Import Frap TransitionSystems.
Require Import List Lia.

(* All variables are by default initialized to 0 *)
Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).

Module IMPLang.
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

Module Big_step.
  Import IMPLang.

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
    | [ H: eval _ (Skip) _ |- _ ] => invert H
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

Module Small_step.
  Import IMPLang Big_step.
  Definition step_state := (valuation * Cmd)%type.

  Inductive step : step_state -> step_state -> Prop :=
  | Step_Assign: forall va x e ve,
    eval_exp va e = ve ->
    step (va, (Assign x e)) (va $+ (x, ve), Skip)
  | Step_Seq0: forall va c1,
    step (va, (Seq Skip c1)) (va, c1)
  | Step_Seq1: forall va va' c0 c0' c1,
    step (va, c0) (va', c0') ->
    step (va, (Seq c0 c1)) (va', (Seq c0' c1))
  | Step_If: forall va be bev th el,
    eval_exp va be = bev ->
    step (va, (If be th el)) (va, if nat_to_bool bev then th else el)
  | Step_While0: forall va be inv body,
    nat_to_bool (eval_exp va be) = false ->
    step (va, (While inv be body)) (va, Skip)
  | Step_While1: forall va be inv body,
    nat_to_bool (eval_exp va be) = true ->
    step (va, (While inv be body)) (va, Seq body (While inv be body))
  | Step_Assert: forall va (a : hassertion),
    a va ->
    step (va, (Assert a)) (va, Skip)
  | Step_Assume: forall va (a : hassertion),
    step (va, (Assume a)) (va, Skip).

  Definition step_trsys_with_init (va : valuation) (code : Cmd) : trsys step_state := {|
    Initial := fun x => x = (va, code);
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
    (* manual proof *)
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

  Lemma multistep_seqctx: forall va c1 c1' c2 va',
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

  Theorem big_to_small: forall code va va',
    eval va code va' -> step ^* (va, code) (va', Skip).
  Proof with (try econstructor; eauto).
    induct 1; simplify.
    + econstructor.
    + econstructor...
    + eapply trc_trans. apply multistep_seqctx. eauto.
      econstructor. econstructor. assumption.
    + econstructor. econstructor. eauto. assumption.
    + econstructor. apply Step_While0... constructor.
    + econstructor. apply Step_While1. equality.
      eapply trc_trans. apply multistep_seqctx. eauto.
      econstructor. econstructor. assumption.
    + econstructor...
    + econstructor...
  Qed.

(* CONFUSED: where does these all JMeq come from? *)

  Lemma small_to_big_one: forall code code' va va',
    step (va, code) (va', code') ->
    forall va'', eval va' code' va'' ->
      eval va code va''.
  Proof with (try econstructor; eauto).
    induct 1; simplify.
    + invert H...
    + econstructor...
    + invert H0. apply IHstep in H4...
    + idtac...
    + invert H0...
    + invert H0...
    + invert H0...
    + invert H...
  Qed.

  Theorem small_to_big: forall code va va',
    step^* (va, code) (va', Skip) -> eval va code va'.
  Proof.
    induct 1; simplify.
    econstructor.

    cases y.
    eapply small_to_big_one.
    eassumption.
    eapply IHtrc; auto.
  Qed.

  Theorem equiv_big_small: forall code va va',
    eval va code va' <-> step^* (va, code) (va', Skip).
  Proof.
    split. apply big_to_small. apply small_to_big.
  Qed.

  (* Example of utilizing composability of big step semantics.
     You'll have pain trying to prove it without the small to big conversion. *)
  Example bigstep_composability: forall va0 va2 c0 c1 c2 c3,
    step^* (va0, Seq c0 (Seq (Seq c1 c2) c3)) (va2, Skip) ->
    exists va1,
      step^* (va0, Seq c0 c1) (va1, Skip) /\ step^* (va1, Seq c2 c3) (va2, Skip).
  Proof.
    intros.
    rewrite <- equiv_big_small in *.
    invert H. invert H5. invert H2.
    exists va5; split;
    rewrite <- equiv_big_small in *;
    econstructor; eauto.
  Qed.
End Small_step.

Module Small_cps.
  Import IMPLang Big_step Small_step.
(*
 * Continuation passing style. Most code inspired by compilerverif.
 *
 * CPS semantics is also small-step semantics with state (va, c, k).
 *  va is the current program store (valuation), c is the focused command, k is the remaining continuation.
 *
 * Transitions can be classified into
 *   + computation: may update va according to c; 'simplifies' c (structurally or semantically); does not change k.
 *   + focusing: move command from c to k, make c simpler and k less simpler; does not change va.
 *   + resumption: move command from k to c, usually when c is done e.g. Skip; does not change va.
 *
 *  Why do we need a Kwhile than replacing it with Kseq (While...)? Still problematic.
 *    Maybe because we do not want each c to contain loops.
 *    So this resembles more the execution process? (series of loop-less basic blocks DAGs)
 *  I tried to do that but when a (While..) comes into the c position, this semantics do not seem much different than naive small step.
 *)
  Inductive Cont :=
  | Cont_Stop
  | Cont_Seq (c : Cmd) (k : Cont)
  | Cont_While (inv : hassertion) (be : Exp) (body : Cmd) (k : Cont).

(* Note that cmd can be while.
   And Cont will have nested Whiles. (the level of iterations)
 *)
  Definition cps_state := (valuation * Cmd * Cont)%type.

  Inductive cps_step : cps_state -> cps_state -> Prop :=
  (* computation *)
  | CpsStep_Assign: forall va x e ve k,
    eval_exp va e = ve ->
    cps_step (va, (Assign x e), k) (va $+ (x, ve), Skip, k)
  | CpsStep_If: forall va be bev th el k,
    eval_exp va be = bev ->
    cps_step (va, (If be th el), k) (va, if nat_to_bool bev then th else el, k)
  | CpsStep_While0: forall va inv be body k,
    nat_to_bool (eval_exp va be) = false ->
    cps_step (va, (While inv be body), k) (va, Skip, k)
  | CpsStep_Assert: forall va (a : hassertion) k,
    a va ->
    cps_step (va, (Assert a), k) (va, Skip, k)
  | CpsStep_Assume: forall va (a : hassertion) k,
    cps_step (va, (Assume a), k) (va, Skip, k)
  (* resumption *)
  | CpsStep_SkipSeq: forall va c k,
    cps_step (va, Skip, Cont_Seq c k) (va, c, k)
  | CpsStep_SkipWhile: forall va inv be body k,
    cps_step (va, Skip, Cont_While inv be body k) (va, While inv be body, k)
  (* focusing *)
  | CpsStep_Seq1: forall va c0 c1 k,
    cps_step (va, (Seq c0 c1), k) (va, c0, Cont_Seq c1 k)
  | CpsStep_While1: forall va inv be body k,
    nat_to_bool (eval_exp va be) = true ->
    cps_step (va, (While inv be body), k) (va, body, Cont_While inv be body k). (* this one has computation too *)


  Definition cps_step_trsys_with_init (va : valuation) (code : Cmd) : trsys cps_state := {|
    Initial := fun x => x = (va, code, Cont_Stop);
    Step := cps_step;
  |}.

  Definition term_cps_step_state (x : cps_state) :=
  match x with
  | (va, cmd, k) => cmd = Skip /\ k = Cont_Stop
  end.

  Example cps_ex0: forall va0 va1,
    reachable (cps_step_trsys_with_init va0 ex0_code) (va1, Skip, Cont_Stop) ->
    va1 $! "x" = va0 $! "x" + 4.
  Proof.
    unfold ex0_code; simplify.

    invert H. simplify. invert H0.
    (* up are initial *)

    invert H1. invert H.
    invert H0. invert H.
    invert H1. invert H.
    invert H0. invert H; simplify.
      invert H7.

    invert H1. invert H.
    invert H0. invert H.
    invert H1. invert H.
    invert H0. invert H.
    invert H1. invert H.
    invert H0. invert H; simplify.
      invert H8.

    invert H1. invert H.
    invert H0. invert H.
    invert H1. invert H.
    invert H0. invert H.
    invert H1. invert H.
    invert H0. invert H; simplify.

    invert H1.
      simplify. lia.
      invert H.
    invert H9.
  Restart.
    Ltac cps_step_invert_one :=
      repeat match goal with
      | [ H : cps_step _ _ |- _ ] => invert H
      end; simplify.

    Ltac cps_step_one :=
      match goal with
      | [ H : cps_step^* _ _ |- _ ] => invert H
      end;
      repeat cps_step_invert_one;
      simplify.

    Ltac cps_step_while :=
      cps_step_one;
      match goal with
      | [ H : nat_to_bool _ = _ |- _ ] => try invert H
      end.
    (* These Ltacs are basically the same as smallstep's *)

    unfold ex0_code; simplify.

    invert H. simplify. invert H0.
    (* up are initial *)

    cps_step_one.
    cps_step_one.
    cps_step_one.
    cps_step_while.
    cps_step_one.
    cps_step_one.
    cps_step_one.
    cps_step_one.
    cps_step_one.
    cps_step_while.
    cps_step_one.
    cps_step_one.
    cps_step_one.
    cps_step_one.
    cps_step_one.
    cps_step_while.
    cps_step_one.
    lia.
  Qed.

(* What challenge will there be if we prove cps_step equivalent to small-step?

   Basically proving equivalence for two TS, we need a equivalence relation.
   And that means a equivalence relation of   cont_apply c k ~ c.
   Note it's a equivalence not equality because structural differences matter the latter but not latter.

   Also we do not have a simple lock-step refinement i.e.
     [Lock-step refinement] cs ~ ss  ->  cps_step cs cs'  ->  step ss ss'  ->  cs' ~ ss'.
   It is too strong.
   Take the focusing & resumption cps steps for example, they are stuttering steps for small-step.

   And program equivalence itself is quite a challenge. So we chose to prove cps_step ~ eval.
*)

  Lemma big_to_cps_kstop_fail: forall code va va',
    eval va code va' ->
    cps_step^* (va, code, Cont_Stop) (va', Skip, Cont_Stop).
  Proof with (repeat (try eassumption; econstructor)).
    induct 1; simplify.
    - idtac...
    - idtac...
    - eapply trc_trans.
      + eapply TrcFront...
      + (* cannot go from here
            We want
                        (va0, c0, Cont_Seq c1 Cont_Stop)
                    ~>* (va2, Skip, Cont_Stop)
            Which is clear by the derivation
                        (va0, c0, Cont_Seq c1 Cont_Stop)
                    ~>* (va1, Skip, Cont_Seq c1 Cont_Stop)  [ by induction ] <***>
                    ~>  (va1, c1, Cont_Stop)                [ by resumption constructor ]
                    ~>* (va2, Skip, Cont_Stop)              [ by induction i.e. IHeval2 ]
            But the step <***> fails: the induction hypothesis only gives
                        (va0, c0, Cont_Stop)
                    ~>* (va1, Skip, Cont_Stop)              [ actual induction hypothesis ]
            The problem arises because we have a too weak hypothesis, imagine a
                    forall k,
                        (va0, c0, k)
                    ~>* (va1, Skip, k)
            Would do.

            So we universally quantify the continuation
         *)
  Abort.

  Theorem big_to_cps_codeonly: forall code va va',
    eval va code va' -> forall k,
    cps_step^* (va, code, k) (va', Skip, k).
  Proof with (repeat (try eassumption; econstructor)).
    induct 1; simplify.
    - idtac...
    - idtac...
    - eapply trc_trans.
      + eapply TrcFront. econstructor. apply IHeval1.
      + econstructor. econstructor. eapply IHeval2.
    - econstructor. econstructor. econstructor. rewrite H. apply IHeval.
    - idtac... equality.
    - eapply trc_trans.
      + eapply TrcFront. apply CpsStep_While1. equality. apply IHeval1.
      + econstructor. econstructor. apply IHeval2.
    - idtac...
    - idtac...
  Qed.

(* Now comes the execution of continuations.
   In an earlier proof I did for compilerverif I defined a big-step semantics for continuations.
   Here I use a denotational approach: convert a continuation into the corresponding command.
   > A continuation basically denotes remaining computation, which can be compiled to commands
*)

  Fixpoint cont_denote_cmd (k : Cont) : Cmd :=
    match k with
    | Cont_Stop => Skip
    | Cont_Seq c k => Seq c (cont_denote_cmd k)
    | Cont_While inv be body k => Seq (While inv be body) (cont_denote_cmd k)
    end.

(* The above denotation function gives semantics to continuations.
   Yet for CPS (va, c, k) we need to include the semantics of c as well.
   The remaining computation is something like $c \oplus k$.

   Naively we can use `(Seq c (cont_denote_cmd k))`.
   Yet it poses challenge for subsequent proofs, because we need $cont_apply c Cont_Stop = c$ (see later comments).
   Therefore we define another version, and prove it's equivalent to `(Seq c (cont_denote_cmd k))`.
    It is really genius insight.
*)

  Fixpoint cont_apply (c : Cmd) (k : Cont) : Cmd :=
      match k with
      | Cont_Stop => c
      | Cont_Seq c1 k => cont_apply (Seq c c1) k
      | Cont_While inv be body k => cont_apply (Seq c (While inv be body)) k
      end.

  (* `cont_apply c k` is equivalent to `(Seq c (cont_denote_cmd k))` for big-step execution. *)
  Lemma cont_apply_split: forall k c va0 va1,
    eval va0 (cont_apply c k) va1 <->
    eval va0 (Seq c (cont_denote_cmd k)) va1.
  Proof with (repeat (try eassumption; econstructor)).
    split; induct k; simplify.
    - idtac...
    - apply IHk in H. bs_simple...
    - apply IHk in H. bs_simple...
    - bs_simple...
    - bs_simple. apply IHk...
    - bs_simple. apply IHk...
  Qed.

  Theorem big_to_cps_cont: forall k c va va',
    eval va (cont_apply c k) va' ->
    cps_step^* (va, c, k) (va', Skip, Cont_Stop).
  Proof.
    induct k; simplify.
    - apply big_to_cps_codeonly. auto.
    - pose proof (IHk _ _ _ H).
      rewrite cont_apply_split in H.
      bs_simple.
      eapply trc_trans. apply big_to_cps_codeonly. eauto.
      econstructor. econstructor.
      eapply trc_trans. apply big_to_cps_codeonly. eauto.
      apply IHk. rewrite cont_apply_split. econstructor. econstructor. auto.
    - pose proof (IHk _ _ _ H).
      rewrite cont_apply_split in H.
      bs_simple.
      eapply trc_trans. apply big_to_cps_codeonly. eauto.
      econstructor. econstructor.
      eapply trc_trans. apply big_to_cps_codeonly. eauto.
      apply IHk. rewrite cont_apply_split. econstructor. econstructor. auto.
  Qed.

  Lemma cps_to_big_codeonly_one: forall c0 c1 va0 va1 va2 k0 k1,
    cps_step (va0, c0, k0) (va1, c1, k1) ->
    eval va1 (cont_apply c1 k1) va2 ->
    eval va0 (cont_apply c0 k0) va2.
  Proof with (repeat (try eassumption; econstructor)).
    induct 1; simplify.
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple.
      econstructor. eapply EvalDefault_While1... auto.
  Qed.

  Theorem cps_to_big_codeonly_fail: forall code va va',
    cps_step^* (va, code, Cont_Stop) (va', Skip, Cont_Stop) ->
    eval va code va'.
  Proof.
    induct 1; simplify.
    econstructor.

    cases y; cases p.
    (* Cannot go from here.
        IHtrc requires `c = Cont_Stop` but H requires `(va, code, Cont_Stop) ~> (v, c0, c)`
        The two conflicts.

        The problem is that the IHtrc is too strong.
        Thus we relax the restrictions by allowing to start from a continuation other than `Cont_Stop`.
     *)
  Abort.

  Theorem cps_to_big_cont: forall code va va' k,
    cps_step^* (va, code, k) (va', Skip, Cont_Stop) ->
    eval va (cont_apply code k) va'.
  Proof.
    induct 1; simplify.
    econstructor.

    cases y; cases p.
    eapply cps_to_big_codeonly_one.
    apply H. apply IHtrc. auto. auto.
  Qed.


  Theorem cps_to_big_codeonly: forall code va va',
    cps_step^* (va, code, Cont_Stop) (va', Skip, Cont_Stop) ->
    eval va code va'.
  Proof.
    intros.
    replace code with (cont_apply code Cont_Stop) by (simplify; auto).
    apply cps_to_big_cont.
    auto.
  Qed.
End Small_cps.


Module Unused.
  (* example: how to do fmap normalization *)
  Goal forall va,
    ((va $+ ("n", 2) $+ ("x", va $! "x" + 2) $+ ("n", 1)) = (va $+ ("n", 1) $+ ("x", va $! "x" + 2))).
  intros. maps_equal. Qed.
End Unused.

Module Failed.
  Import IMPLang Big_step Small_step Small_cps.
  Ltac ec := econstructor.
  Ltac ea := eassumption.

  (* try prove CPS reduction like a frame rule: before we're done with the current c, we wont touch the k. *)
  Lemma cps_local_exec_fail: forall c0 va0 va2 k0,
    cps_step^* (va0, c0, k0) (va2, Skip, Cont_Stop) ->
    exists va1,
      cps_step^* (va0, c0, k0) (va1, Skip, k0) /\
      cps_step^* (va1, Skip, k0) (va2, Skip, Cont_Stop).
  Proof.
    induct c0; simplify.
    - eexists. split.
      ec. auto.
    - invert H. invert H0.
      eexists. split.
      ec. ec. ec. ec. auto.
    - rename c0_1 into c0; rename c0_2 into c1.
      invert H. invert H0. apply IHc0_1 in H1. cases H1. cases H.
      invert H0. invert H1. apply IHc0_2 in H2. cases H2. cases H0.
      rename x into va10. rename x0 into va11. rename va2 into va3.
      eexists. split.
      ec. ec. eapply trc_trans. ea. ec. ec. ea. ea.
    - rename c0_1 into th; rename c0_2 into el.
      invert H. invert H0. cases (nat_to_bool (eval_exp va0 be)).
      + apply IHc0_1 in H1. cases H1. cases H.
        eexists. ec. ec. ec. ec. rewrite Heq. ea. ea.
      + apply IHc0_2 in H1. cases H1. cases H.
        eexists. ec. ec. ec. ec. rewrite Heq. ea. ea.
    - rename c0 into body.
      (* this subgoal we have problems *)
      invert H. invert H0; simplify.
      + (* while not taken *)
        eexists. split.
        ec. ec. ea. ec. ea.
      + apply IHc0 in H1. cases H1. cases H.
        rename x into va1. eexists. split.
        ec. apply CpsStep_While1. ea.
        (* cannot go from here.
            We want to prove      (va0, body, Cont_While inv be body k0) ~>* (?va1, Skip, k0)
            But we have by IH     (va0, body, Cont_While inv be body k0) ~>* ( va1, Skip, Cont_While inv be body k0)
            The latter is just one iteration but the former is many iterations.

            The problem is on the induction hypothesis...
         *)
    Abort.

  Lemma cps_expand_cont: forall k va va' code,
    cps_step^* (va, code, k) (va', Skip, Cont_Stop) ->
    cps_step^* (va, (cont_apply code k), Cont_Stop) (va', Skip, Cont_Stop).
  Proof.
  Abort.

  Lemma cps_multistep_kctx: forall code va va' k1,
    cps_step^* (va, code, k1) (va', Skip, k1) -> forall k2,
    cps_step^* (va, code, k2) (va', Skip, k2).
  Proof.
  Abort.

End Failed.
