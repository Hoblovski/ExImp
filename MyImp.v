(* The one single file (that compiles very slow) of PLV techniques experimented on IMP *)

Require Import List Lia ZArith.
Require Import Frap TransitionSystems.


Arguments Z.mul: simpl never.
Arguments Z.add: simpl never.
Open Scope Z.
(* All variables are by default initialized to 0 *)
Notation "m $! k" := (match m $? k with Some n => n | None => 0 end)%Z (at level 30).

Module IMPLang.
  (* Definition of the IMP language and denotational/operational semantics of expressions *)
  Notation Value := Z.

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

  Inductive Cmd :=
  | Skip
  | Assign (x : var) (e : Exp)
  | Seq (c1 c2 : Cmd)
  | If (be : Exp) (th el : Cmd)
  | While (be : Exp) (body : Cmd)
  | Assert (be : Exp).

  Definition to_bool {A B} (s : sumbool A B) := if s then true else false.

  Definition value_to_bool (n : Value) := negb (n =? 0).
  Definition bool_to_value (b : bool) := if b then 1 else 0.

  Lemma bool_to_value_to_bool: forall v,
    value_to_bool (bool_to_value v) = v.
  Proof.
    destruct v; simplify; auto.
  Qed.

  Definition denote_unaopkind (k : UnaopKind) : Value -> Value :=
    match k with
     | Lnot => fun x => bool_to_value (negb (value_to_bool x))
    end.

  Definition denote_binopkind (k : BinopKind) : Value -> Value -> Value :=
    match k with
     | Plus => fun x y => x + y
     | Minus => fun x y => x - y
     | Mul => fun x y => x * y
     | Eq => fun x y => bool_to_value (x =? y)
     | Le => fun x y => bool_to_value (x <=? y)
     | Land => fun x y => bool_to_value (value_to_bool x && value_to_bool y)
     | Lor => fun x y => bool_to_value (value_to_bool x || value_to_bool y)
    end.

  Fixpoint eval_exp (va : valuation) (e : Exp) : Value :=
    match e with
    | Const n => n
    | Var x => va $! x
    | Unaop op e =>
      let opv := (denote_unaopkind op) in
      let ev := eval_exp va e in
      opv ev
    | Binop op e1 e2 =>
      let opv := (denote_binopkind op) in
      let e1v := eval_exp va e1 in
      let e2v := eval_exp va e2 in
      opv e1v e2v
    end.
  Definition denote_exp (e : Exp) : valuation -> Value :=
    fun va => eval_exp va e.

  Coercion Const : Z >-> Exp.
  Coercion Var : string >-> Exp.
  Example ex0_code :=
    (Seq
      (Assign "n" 2)
      (While (Unaop Lnot (Binop Eq 0 "n"))
        (Seq
          (Assign "x" (Binop Plus "x" 2))
          (Assign "n" (Binop Minus "n" 1))))).
End IMPLang.

Module Big_step.
  Import IMPLang.

  (* relational big step *)
  Inductive eval : valuation -> Cmd -> valuation -> Prop :=
  | Eval_Skip: forall va,
    eval va Skip va
  | Eval_Assign: forall va x e ve,
    eval_exp va e = ve ->
    eval va (Assign x e) (va $+ (x, ve))
  | Eval_Seq: forall va0 va1 va2 c0 c1,
    eval va0 c0 va1 ->
    eval va1 c1 va2 ->
    eval va0 (Seq c0 c1) va2
  | Eval_If: forall va0 va1 be bev th el,
    eval_exp va0 be = bev ->
    eval va0 (if (value_to_bool bev) then th else el) va1 ->
    eval va0 (If be th el) va1
  | Eval_While0: forall va0 be body,
    value_to_bool (eval_exp va0 be) = false ->
    eval va0 (While be body) va0
  | Eval_While1: forall va0 va1 va2 be body,
    value_to_bool (eval_exp va0 be) = true ->
    eval va0 body va1 ->
    eval va1 (While be body) va2 ->
    eval va0 (While be body) va2
  | Eval_Assert: forall va be,
    value_to_bool (eval_exp va be) = true ->
    eval va (Assert be) va.


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
    | [ H: eval _ (While _ _) _ |- _ ] => invert H
    end; simplify;
    match goal with
    | [ H : value_to_bool _ = _ |- _ ] => try invert H
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
    step (va, (If be th el)) (va, if value_to_bool bev then th else el)
  | Step_While0: forall va be body,
    value_to_bool (eval_exp va be) = false ->
    step (va, (While be body)) (va, Skip)
  | Step_While1: forall va be body,
    value_to_bool (eval_exp va be) = true ->
    step (va, (While be body)) (va, Seq body (While be body))
  | Step_Assert: forall va be,
    value_to_bool (eval_exp va be) = true ->
    step (va, (Assert be)) (va, Skip).

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
    | [ H : value_to_bool _ = _ |- _ ] => try invert H
    end.

    unfold ex0_code. intros. intros.

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
    eauto.
    simplify. lia.
    invert H.
  Qed.

  (* stronger version: guarantee to terminate *)
  Example smallstep_ex0': forall va0, exists va1,
      reachable (step_trsys_with_init va0 ex0_code) (va1, Skip) /\
      va1 $! "x" = va0 $! "x" + 4.
  Proof.
    unfold ex0_code. intros. eexists.
    split.

    econstructor.
    econstructor.
    simplify.

    Ltac ec_but_while :=
      match goal with
      | [ |- step (_, While _ _) _ ] => fail 1
      | _ => econstructor
      end.

    eapply TrcFront. apply Step_Seq1.
      apply Step_Assign. auto.
    eapply TrcFront. apply Step_Seq0.
    simplify.

    eapply TrcFront. apply Step_While1.
      simplify; auto.
    eapply TrcFront.
      apply Step_Seq1. apply Step_Seq1.
      apply Step_Assign. auto.
    eapply TrcFront.
      apply Step_Seq1. apply Step_Seq0.
    eapply TrcFront.
      apply Step_Seq1. apply Step_Assign. auto.
    eapply TrcFront.
      apply Step_Seq0.
    simplify.

    eapply TrcFront. apply Step_While1.
      simplify; auto.
    eapply TrcFront.
      apply Step_Seq1. apply Step_Seq1.
      apply Step_Assign. auto.
    eapply TrcFront.
      apply Step_Seq1. apply Step_Seq0.
    eapply TrcFront.
      apply Step_Seq1. apply Step_Assign. auto.
    eapply TrcFront.
      apply Step_Seq0.
    simplify.

    eapply TrcFront. apply Step_While0.
      simplify; auto.
    apply TrcRefl.

    simplify; lia.
  Qed.
  (* For now we do not consider termination ... Hoare logic did not incorporate loop ranks yet *)

  Lemma multistep_seqctx: forall va c1 c1' c2 va',
    step^* (va, c1) (va', c1') ->
    step^* (va, Seq c1 c2) (va', Seq c1' c2).
  Proof.
  (* The key to coq thinking is inducting on proofs *)
    induct 1%nat.
    + constructor.
    + cases y.
      econstructor.
      constructor. eassumption.
      apply IHtrc; auto.
  Qed.

  Theorem big_to_small: forall code va va',
    eval va code va' -> step ^* (va, code) (va', Skip).
  Proof with (try econstructor; eauto).
    induct 1%nat; simplify.
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
  Qed.

(* CONFUSED: where does these all JMeq come from? *)

  Lemma small_to_big_one: forall code code' va va',
    step (va, code) (va', code') ->
    forall va'', eval va' code' va'' ->
      eval va code va''.
  Proof with (try econstructor; eauto).
    induct 1%nat; simplify.
    + invert H...
    + econstructor...
    + invert H0. apply IHstep in H4...
    + idtac...
    + invert H0...
    + invert H0...
    + invert H0...
  Qed.

  Theorem small_to_big: forall code va va',
    step^* (va, code) (va', Skip) -> eval va code va'.
  Proof.
    induct 1%nat; simplify.
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
  | Cont_While (be : Exp) (body : Cmd) (k : Cont).

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
    cps_step (va, (If be th el), k) (va, if value_to_bool bev then th else el, k)
  | CpsStep_While0: forall va be body k,
    value_to_bool (eval_exp va be) = false ->
    cps_step (va, (While be body), k) (va, Skip, k)
  | CpsStep_Assert: forall va be k,
    value_to_bool (eval_exp va be) = true ->
    cps_step (va, (Assert be), k) (va, Skip, k)
  (* resumption *)
  | CpsStep_SkipSeq: forall va c k,
    cps_step (va, Skip, Cont_Seq c k) (va, c, k)
  | CpsStep_SkipWhile: forall va be body k,
    cps_step (va, Skip, Cont_While be body k) (va, While be body, k)
  (* focusing *)
  | CpsStep_Seq1: forall va c0 c1 k,
    cps_step (va, (Seq c0 c1), k) (va, c0, Cont_Seq c1 k)
  | CpsStep_While1: forall va be body k,
    value_to_bool (eval_exp va be) = true ->
    cps_step (va, (While be body), k) (va, body, Cont_While be body k). (* this one has computation too *)


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
      invert H6.

    invert H1. invert H.
    invert H0. invert H.
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

    invert H1.
      simplify. lia.
      invert H.
    invert H8.
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
      | [ H : value_to_bool _ = _ |- _ ] => try invert H
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
    induct 1%nat; simplify.
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
    induct 1%nat; simplify.
    - idtac...
    - idtac...
    - eapply trc_trans.
      + eapply TrcFront. econstructor. apply IHeval1.
      + econstructor. econstructor. eapply IHeval2.
    - econstructor. econstructor. econstructor. rewrite H. apply IHeval.
    - idtac...
    - eapply trc_trans.
      + eapply TrcFront. apply CpsStep_While1. equality. apply IHeval1.
      + econstructor. econstructor. apply IHeval2.
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
    | Cont_While be body k => Seq (While be body) (cont_denote_cmd k)
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
      | Cont_While be body k => cont_apply (Seq c (While be body)) k
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

  Lemma big_to_cps_cont: forall k c va va',
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

  Lemma cps_to_big_one: forall c0 c1 va0 va1 va2 k0 k1,
    cps_step (va0, c0, k0) (va1, c1, k1) ->
    eval va1 (cont_apply c1 k1) va2 ->
    eval va0 (cont_apply c0 k0) va2.
  Proof with (repeat (try eassumption; econstructor)).
    induct 1%nat; simplify.
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple...
    - rewrite cont_apply_split in *. bs_simple.
      econstructor. eapply Eval_While1... auto.
  Qed.

  Lemma cps_to_big_code_fail: forall code va va',
    cps_step^* (va, code, Cont_Stop) (va', Skip, Cont_Stop) ->
    eval va code va'.
  Proof.
    induct 1%nat; simplify.
    econstructor.

    cases y; cases p.
    (* Cannot go from here.
        IHtrc requires `c = Cont_Stop` but H requires `(va, code, Cont_Stop) ~> (v, c0, c)`
        The two conflicts.

        The problem is that the IHtrc is too strong.
        Thus we relax the restrictions by allowing to start from a continuation other than `Cont_Stop`.
     *)
  Abort.

  Lemma cps_to_big_cont: forall code va va' k,
    cps_step^* (va, code, k) (va', Skip, Cont_Stop) ->
    eval va (cont_apply code k) va'.
  Proof.
    induct 1%nat; simplify.
    econstructor.

    cases y; cases p.
    eapply cps_to_big_one.
    apply H. apply IHtrc. auto. auto.
  Qed.

  Lemma cps_to_big_code: forall code va va',
    cps_step^* (va, code, Cont_Stop) (va', Skip, Cont_Stop) ->
    eval va code va'.
  Proof.
    intros.
    replace code with (cont_apply code Cont_Stop) by (simplify; auto).
    apply cps_to_big_cont.
    auto.
  Qed.

  Theorem equiv_big_cps: forall code va va' k,
    cps_step^* (va, code, k) (va', Skip, Cont_Stop) <->
    eval va (cont_apply code k) va'.
  Proof.
    split. apply cps_to_big_cont. apply big_to_cps_cont.
  Qed.

  Theorem equiv_big_cps_code: forall code va va',
    cps_step^* (va, code, Cont_Stop) (va', Skip, Cont_Stop) <->
    eval va code va'.
  Proof.
    intros. apply equiv_big_cps.
  Qed.

  Lemma cps_to_small_cont:  forall code va va' k,
    cps_step^* (va, code, k) (va', Skip, Cont_Stop) ->
    step^* (va, cont_apply code k) (va', Skip).
  Proof.
    intros. apply big_to_small. apply cps_to_big_cont. auto.
  Qed.

  Lemma small_to_cps_cont:  forall code va va' k,
    step^* (va, cont_apply code k) (va', Skip) ->
    cps_step^* (va, code, k) (va', Skip, Cont_Stop).
  Proof.
    intros. apply big_to_cps_cont. apply small_to_big. auto.
  Qed.

  Theorem equiv_small_cps: forall code va va' k,
    step^* (va, cont_apply code k) (va', Skip) <->
    cps_step^* (va, code, k) (va', Skip, Cont_Stop).
  Proof.
    split. apply small_to_cps_cont. apply cps_to_small_cont.
  Qed.
End Small_cps.

Module IMPHoare.
  Import IMPLang.

  Definition hprop := valuation -> Prop.
  Definition hprop_true : hprop := fun va => True.
  Definition hprop_false : hprop := fun va => False.
  (* Note the return types. *)
  Definition himply (p q : hprop) : Prop := forall va, p va -> q va.
  Definition andh (p q : hprop) : hprop := fun va => p va /\ q va.
  Definition noth (p : hprop) : hprop := fun va => ~ p va.

  Lemma himply_refl: forall p, himply p p.
  Proof.
    unfold himply; intuition.
  Qed.
  Hint Resolve himply_refl : core.
  Lemma himply_trans: forall p q r, himply p q -> himply q r -> himply p r.
  Proof.
    unfold himply; intuition.
  Qed.
  Hint Resolve himply_trans : core.
  Lemma himply_andh: forall p q, himply (andh p q) p.
  Proof.
    unfold himply; unfold andh; intuition.
  Qed.
  Hint Resolve himply_andh : core.
  Lemma himply_andh_comm: forall p q, himply (andh p q) (andh q p).
  Proof.
    unfold himply; unfold andh; intuition.
  Qed.
  Hint Resolve himply_andh_comm : core.

  Lemma andh_sem: forall p q va, p va /\ q va <-> andh p q va.
  Proof.
    unfold andh; intuition.
  Qed.
  Lemma himply_sem: forall p q va, himply p q -> p va -> q va.
  Proof.
    unfold himply; intuition.
  Qed.

  (* used to convert a IMP proposition (boolean expr) to a logical proposition (hoare assertion) *)
  Definition hprop_bexp (e : Exp) : hprop := fun va => value_to_bool (eval_exp va e) = true.

  Lemma hprop_eval_true: forall va be, value_to_bool (eval_exp va be) = true <-> hprop_bexp be va.
  Proof.
    unfold hprop_bexp. intuition.
  Qed.
  Lemma hprop_eval_false: forall va be, value_to_bool (eval_exp va be) = false <-> noth (hprop_bexp be) va.
  Proof.
    unfold hprop_bexp. unfold noth. intros. rewrite not_true_iff_false. intuition.
  Qed.

(* Many flavours of hoare triples exist.

   For example, assignment is usually written in a backwards fashion a.k.a. the Hoare rule
      {{ P[e/x] }}  x=e  {{ P }}    [ HT_Assignment ]
   Or in a forward fashion a.k.a. the Floyd rule
      fresh x'
      -----------
      {{ x=x' }}  x=e  {{ x = e[x'/x] }}

  Actually floyd rule makes verification harder, because it introduces quantifiers to assertions.
  SF uses the hoare rule, and FRAP uses floyd rule.
*)

  Module FloydAssign.
    Inductive hoare_triple : hprop -> Cmd -> hprop -> Prop :=
    (* computation *)
    | HT_Skip: forall p,
      hoare_triple p Skip p
    | HT_Assign: forall p x e,
      hoare_triple p (Assign x e) (fun va => exists va', p va' /\ va = va' $+ (x, eval_exp va' e))
    | HT_If: forall p q be th el,
      hoare_triple (andh p (fun va => value_to_bool (eval_exp va be) = true))  th q ->
      hoare_triple (andh p (fun va => value_to_bool (eval_exp va be) = false)) el q ->
      hoare_triple p (If be th el) q
    | HT_Seq: forall p q r c0 c1,
      hoare_triple p c0 r ->
      hoare_triple r c1 q ->
      hoare_triple p (Seq c0 c1) q
    | HT_While: forall p q inv be body,
      himply p inv ->
      himply (andh inv (fun va => value_to_bool (eval_exp va be) = false)) q ->
      hoare_triple (andh inv (fun va => value_to_bool (eval_exp va be) = true)) body inv ->
      hoare_triple p (While be body) q
    | HT_Assert: forall p be,
      himply p (fun va => value_to_bool (eval_exp va be) = true) ->
      hoare_triple p (Assert be) p
    (* meta transformation *)
    | HT_Conseq: forall p q p' q' c,
      himply p' p ->
      himply q q' ->
      hoare_triple p c q ->
      hoare_triple p' c q'.

    Lemma HT_Post: forall p c q q',
      hoare_triple p c q ->
      himply q q' ->
      hoare_triple p c q'.
    Proof.
      eauto using hoare_triple.
    Qed.

    Lemma HT_Pre: forall p c q p',
      hoare_triple p c q ->
      himply p' p ->
      hoare_triple p' c q.
    Proof.
      eauto using hoare_triple.
    Qed.

    (* a few pitfalls:
        use Z than nat for value. subtraction of nat is hell.
        precondition requires *)
    Example hoare_ex0: forall x0,
      hoare_triple (fun va => va $! "x" = x0) ex0_code (fun va => va $! "n" = 0 /\ va $! "x" = x0 + 4).
    Proof.
    Abort.
  End FloydAssign.

  Module HoareAssign.
    Inductive hoare_triple : hprop -> Cmd -> hprop -> Prop :=
    (* computation *)
    | HT_Skip: forall p,
      hoare_triple p Skip p
    | HT_Assign: forall q x e,
      hoare_triple (fun va => q (va $+ (x, eval_exp va e))) (Assign x e) q
    | HT_If: forall p q be th el,
      hoare_triple (andh p (hprop_bexp be)) th q ->
      hoare_triple (andh p (noth (hprop_bexp be))) el q ->
      hoare_triple p (If be th el) q
    | HT_Seq: forall p q r c0 c1,
      hoare_triple p c0 r ->
      hoare_triple r c1 q ->
      hoare_triple p (Seq c0 c1) q
    | HT_While: forall inv be body,
      hoare_triple (andh inv (hprop_bexp be)) body inv ->
      hoare_triple inv (While be body) (andh inv (noth (hprop_bexp be)))
    | HT_Assert: forall p be,
      himply p (fun va => value_to_bool (eval_exp va be) = true) ->
      hoare_triple p (Assert be) p
    (* meta transformation *)
    | HT_Conseq: forall p q p' q' c,
      hoare_triple p c q ->
      himply p' p ->
      himply q q' ->
      hoare_triple p' c q'.

    Lemma HT_Post: forall p c q q',
      hoare_triple p c q ->
      himply q q' ->
      hoare_triple p c q'.
    Proof.
      eauto using hoare_triple.
    Qed.

    Lemma HT_Pre: forall p c q p',
      hoare_triple p c q ->
      himply p' p ->
      hoare_triple p' c q.
    Proof.
      eauto using hoare_triple.
    Qed.

    Example hoare_ex0: forall x0,
      hoare_triple (fun va => va $! "x" = x0) ex0_code (fun va => va $! "n" = 0 /\ va $! "x" = x0 + 4).
    Proof.
      (* this shit is so manual... especially handling Seq. needs automation!
       * Automation will be introduced in the WP calculus module.
       *)
      unfold ex0_code; intros.
      remember (fun va => va$!"n">=0 /\ (2*(va$!"n")+(va$!"x")=x0+4)) as inv.
      remember (Unaop Lnot (Binop Eq 0 "n")) as be.
      apply HT_Seq with inv.
      + eapply HT_Pre. apply HT_Assign. (* This is how stupid assignments are handled... First Pre then Assign *)
        intro va. rewrite Heqinv. simplify. lia.
      + apply HT_Post with (andh inv (noth (hprop_bexp be))).
        - apply HT_While.
          apply HT_Seq with (fun va => va$!"n" >= 1 /\ 2*(va$!"n") + (va$!"x") = x0 + 6).
          * eapply HT_Pre. eapply HT_Assign.
            intro va. unfold andh. unfold hprop_bexp. subst. simplify. repeat rewrite bool_to_value_to_bool in *. intuition.
            cases (va$!"n"); simplify; try discriminate; lia.
          * eapply HT_Pre. eapply HT_Assign.
            intro va. subst. simplify. lia.
        - intro va. unfold andh. unfold noth. unfold hprop_bexp. subst. simplify.
          repeat rewrite bool_to_value_to_bool in *.
          cases (va$!"n"); simplify; try discriminate; try lia.
          intuition.
    Qed.

    Import Big_step.
    (* In the previous versions we have Assume in Imp which render Hoare Logic Unsound.
     * So we needed a precondition like `assume_free`.
     * Now we've stripped assume from raw Hoare Logic. *)
    Theorem hoare_sound: forall p c q,
      hoare_triple p c q ->
      forall va va',
        p va ->
        eval va c va' ->
        q va'.
    Proof.
      induct 1%nat; simplify;
        try (bs_simple; assumption).
      - invert H2. cases (value_to_bool (eval_exp va be)).
        + eapply IHhoare_triple1; eauto. intuition. rewrite <- andh_sem. eauto.
        + eapply IHhoare_triple2; eauto. intuition. rewrite <- andh_sem. rewrite <- hprop_eval_false. eauto.
      - invert H2.
        eauto.
      - induct H1; simplify. (* induction on the number of iterations *)
        + rewrite <- andh_sem. split; eauto. rewrite <- hprop_eval_false; eauto.
        + assert (inv va1). { eapply IHhoare_triple; eauto. rewrite <- andh_sem; eauto. }
          apply (IHeval2 be body); eauto. (* why must this apply have args *)
      - invert H1. eauto.
      - eapply himply_sem; eauto.
    Qed.
    (* Of course we cannot have a completeness theorem for hoare logic... *)
  End HoareAssign.
  Export HoareAssign.

  Module HoareAnnot.
    (* Annotated programs make vcgen possible. They are called 'decorated programs' in SF. *)
    (* TODO: wlp *)
  End HoareAnnot.
End IMPHoare.

Module Stack_machine.
  Import IMPLang.
  Open Scope nat.

  (* Actually stack is a list (consecutive nat -> Value).
     During compilation each variable will be assigned an index.
     For simplifity we use valuation (var -> Value),
      which combines the frame result (var -> nat) and the stack lookup (nat -> Value).

     We structurally separate variable section and expression section.
     The former is the `valuation`, and the latter is the `list Value`.
     And name them `vstk` and `estk` correspondingly.

     We make PC to be nat rather than Z and represent backwards jump with a `bwdir` flag.
     This is different from compilerverif since we use coq standard library for instrs.
     So nat's work better with `length` etc.
     And naturally we enforce the constraint pc>=0.
     Note that pc subtraction could underflow for nat i.e. pc - offset + offset != pc.

     Note the stack machine state is not parametrized by code (list stack_instr).
     The transition system is, instead.
     That's more reasonable for not self-modifying code and makes proof easier.
   *)
  Definition stk_state := (nat * valuation * list Value)%type. (* (pc, vars, expr stack) *)

  Inductive stack_instr :=
  | StkConst (v : Value)
  | StkLoadVar (x : var)
  | StkStoreVar (x : var)
  | StkUnary (op : UnaopKind)
  | StkBinary (op : BinopKind)
  | StkCondJump (bwdir : bool) (offset : nat)
  | StkNoop
  | StkHalt
  | StkUnreachable. (* Also used as panic *)
  (* shorthands *)
  Definition StkCondJumpBw := StkCondJump true.
  Definition StkCondJumpFw := StkCondJump false.

  Arguments app: simpl never. (* so sequences of instrs are always in terms of ++ *)
  (* TODO: all use instrs at. this helps automation and reduce useless conversions *)
  Inductive instr_at: list stack_instr -> nat -> stack_instr -> Prop :=
  | MkInstrAt: forall instrs pc instr,
    instr = nth pc instrs StkUnreachable ->
    instr_at instrs pc instr.

  (* could be defined as `sublist (pc, pc + length instrs) = instrs`, but that's more cumbersome *)
  Inductive instrs_at : list stack_instr -> nat -> list stack_instr -> Prop :=
  | MkInstrsAt: forall ibefore instrs iafter pc,
    length ibefore = pc ->
    instrs_at (ibefore ++ instrs ++ iafter) pc instrs.

  (* shorthand *)
  Definition condgoto_dst arg (bwdir : bool) offset pc :=
    if value_to_bool arg then
      if bwdir then pc - offset else pc + offset
    else
      pc + 1.

  Inductive stk_step (instrs : list stack_instr) : stk_state -> stk_state -> Prop :=
  | StkStep_Const: forall pc vstk estk v,
    instr_at instrs pc (StkConst v) ->
    stk_step instrs
      (pc, vstk, estk)
      (pc + 1, vstk, v :: estk)
  | StkStep_LoadVar: forall pc vstk estk x,
    instr_at instrs pc (StkLoadVar x) ->
    stk_step instrs
      (pc, vstk, estk)
      (pc + 1, vstk, (vstk $! x) :: estk)
  | StkStep_StoreVar: forall pc vstk estk x arg,
    instr_at instrs pc (StkStoreVar x) ->
    stk_step instrs
      (pc, vstk, arg :: estk)
      (pc + 1, vstk $+ (x, arg), estk)
  | StkStep_Unary: forall pc vstk estk arg op,
    instr_at instrs pc (StkUnary op) ->
    stk_step instrs
      (pc, vstk, arg :: estk)
      (pc + 1, vstk, (denote_unaopkind op arg) :: estk)
  | StkStep_Binary: forall pc vstk estk arg0 arg1 op,
    instr_at instrs pc (StkBinary op) ->
    stk_step instrs
      (pc, vstk, arg1 :: arg0 :: estk)
      (pc + 1, vstk, (denote_binopkind op arg0 arg1) :: estk)
  | StkStep_CondJump: forall pc vstk estk arg bwdir offset,
    instr_at instrs pc (StkCondJump bwdir offset) ->
    stk_step instrs
      (pc, vstk, arg :: estk)
      (condgoto_dst arg bwdir offset pc, vstk, estk)
  | StkStep_Noop: forall pc vstk estk,
    instr_at instrs pc StkNoop ->
    stk_step instrs (pc, vstk, estk)
      (pc + 1, vstk, estk).

  (* start from pc=0, empty variable map and empty expression stack *)
  Definition stk_trsys_with_init (pc : nat) (instrs : list stack_instr)
      (vstk : valuation) (estk : list Value): trsys stk_state := {|
    Initial := fun x => x = (pc, vstk, estk);
    Step := stk_step instrs;
  |}.

  Fixpoint compile_exp_to_stk (e : Exp) : list stack_instr :=
    match e with
    | Const n => [ StkConst n ]
    | Var x => [ StkLoadVar x ]
    | Unaop op e => compile_exp_to_stk e ++ [ StkUnary op ]
    | Binop op e1 e2 => compile_exp_to_stk e1 ++ compile_exp_to_stk e2 ++ [ StkBinary op ]
    end.

  Fixpoint compile_cmd_to_stk (c : Cmd) : list stack_instr :=
    match c with
    | Skip =>
      [ ] (* not no-op? because that makes proof go bad *)
    | Assign x e =>
      compile_exp_to_stk e ++ [ StkStoreVar x ]
    | Seq c1 c2 =>
      compile_cmd_to_stk c1 ++ compile_cmd_to_stk c2
    | If be th el =>
      compile_exp_to_stk be ++
      [ StkCondJumpFw (1 + length (compile_cmd_to_stk el) + 1 + 1) ] ++
      compile_cmd_to_stk el ++
      [ StkConst 1 ] ++
      [ StkCondJumpFw (1 + length (compile_cmd_to_stk th)) ] ++
      compile_cmd_to_stk th
    | While be body =>
      compile_exp_to_stk be ++
      [ StkUnary Lnot ] ++
      [ StkCondJumpFw (1 + length (compile_cmd_to_stk body) + 1 + 1) ] ++
      compile_cmd_to_stk body ++
      [ StkConst 1 ] ++
      [ StkCondJumpBw (1 + length (compile_cmd_to_stk body) + 1 + 1 + length (compile_exp_to_stk be)) ]
      (* This writing makes automation easier *)
    | Assert be =>
      compile_exp_to_stk be ++
      [ StkCondJumpFw (1 + 1) ] ++
      [ StkUnreachable ]
    end.

  Compute compile_cmd_to_stk ex0_code.

  (* TODO *)
  Example ex0_stk: Prop.
  Proof.
  Abort.

  Lemma instrs_at_nil: forall ibefore iafter,
    instrs_at (ibefore ++ iafter) (length ibefore) [].
  Proof.
    simplify. rewrite <- (app_nil_r ibefore). rewrite <- app_assoc.
    econstructor. rewrite app_length. auto.
  Qed.
  Lemma instr_at_ibefore_1: forall ibefore instr iafter,
    instr_at (ibefore ++ [ instr ] ++ iafter) (length ibefore) instr.
  Proof.
    Arguments app : simpl nomatch.
    simplify. econstructor. rewrite nth_middle. auto.
  Qed.
  Arguments app : simpl never.
  Lemma instr_at_ibefore_2: forall ibefore0 ibefore1 instr iafter,
    instr_at (ibefore0 ++ ibefore1 ++ [ instr ] ++ iafter) (length ibefore0 + length ibefore1) instr.
  Proof.
    intros.
    repeat (rewrite <- app_length; rewrite app_assoc; try apply instr_at_ibefore_1).
  Qed.
  Lemma instr_at_ibefore_3: forall ibefore0 ibefore1 ibefore2 instr iafter,
    instr_at (ibefore0 ++ ibefore1 ++ ibefore2 ++ [ instr ] ++ iafter) (length ibefore0 + length ibefore1 + length ibefore2) instr.
  Proof.
    intros.
    repeat (rewrite <- app_length; rewrite app_assoc; try apply instr_at_ibefore_1).
  Qed.
  Lemma instrs_at_ibefore_1: forall ibefore instrs instr iafter i,
    (i < length instrs)%nat ->
    instr = (nth i instrs StkUnreachable) ->
    instr_at (ibefore ++ instrs ++ iafter) (length ibefore + i)%nat instr.
  Proof.
    econstructor. rewrite app_nth2_plus. rewrite app_nth1; auto.
  Qed.

  (* Thank compilerverif for the auto and autorewrite techniques *)
  Hint Resolve instr_at_ibefore_1 instr_at_ibefore_2 instr_at_ibefore_3 : instrs.
  (* Normalize instr_at: make instrs and pc addition to be rassoc. Split len(l1++l2). *)
  Hint Rewrite app_assoc_reverse app_length plus_assoc_reverse Nat.add_0_r app_nil_l: instrs.

  Open Scope nat.
  (* instrs_at (done0 + done1 + rest) (len done0 + len done1 + x) y
     ===>
     instrs_at (done3         + rest) (len done3             + x) y
   *)
Check plus_assoc.
  Ltac instr_at_fold_one :=
    try match goal with
    | [ |- instrs_at (?done ++ _ ++ _) (length ?done + (?l1 + ?l2)) _ ] => rewrite (plus_assoc (length done) l1 l2) (*rewrite (plus_assoc (length ?done) l1 l2)*)
    end;
    match goal with
    | [ |- (instrs_at (?a ++ ?b ++ _)) (length ?a + ?l) _ ] =>
      rewrite app_assoc at 1;
      replace (length a + l) with (length a + length b) by auto;
      rewrite <- app_length at 1
    | [ |- (instrs_at (?a ++ ?b ++ _ )) (length ?a + ?l + _) _ ] =>
      rewrite app_assoc at 1;
      replace (length a + l) with (length a + length b) by auto;
      rewrite <- app_length at 1
    end.
  (* instrs_at (l1 ++ ... ++ lk ++ rest) (len l1 + ... + len lk) lk
     ===> T
  *)
  Ltac instr_at_auto :=
    repeat match goal with
    | [ |- instrs_at (_ ++ _ ++ _) (((?a0 + ?a1) + ?b) + ?c) _ ] => rewrite <- (plus_assoc (a0+a1) b c)
    end;
    repeat instr_at_fold_one; (apply instrs_at_nil || constructor); auto with instrs.

  (*
    stk_step (done0 ++ done1 ++ rest) (len done0 + len done1 + _, _, _) _
    ===>
    stk_step (done2          ++ rest) (len done2             + _, _, _) _
   *)
  Ltac stk_step_fold_one :=
    match goal with
    | [ |- stk_step (?done0 ++ ?done1 ++ ?rest) ((length ?done0 + length ?done1)%nat, _, _) _ ] =>
      rewrite (app_assoc done0 done1 rest);
      rewrite <- (app_length done0 done1)
    | [ |- stk_step (?done0 ++ ?done1 ++ ?rest) ((length ?done0 + length ?done1 + _)%nat, _, _) _ ] =>
      rewrite (app_assoc done0 done1 rest);
      rewrite <- (app_length done0 done1)
    | [ |- (stk_step (?done0 ++ ?done1 ++ ?rest)) ^* ((length ?done0 + length ?done1)%nat, _, _) _ ] =>
      rewrite (app_assoc done0 done1 rest);
      rewrite <- (app_length done0 done1)
    | [ |- (stk_step (?done0 ++ ?done1 ++ ?rest)) ^* ((length ?done0 + length ?done1 + _)%nat, _, _) _ ] =>
      rewrite (app_assoc done0 done1 rest);
      rewrite <- (app_length done0 done1)
    end.

  Lemma compile_exp_ok: forall e einstrs,
    compile_exp_to_stk e = einstrs ->
    forall pc instrs vstk estk,
      instrs_at instrs pc einstrs ->
      (stk_step instrs)^* (pc, vstk, estk) ((pc + length einstrs)%nat, vstk, eval_exp vstk e :: estk).
  Proof.
    induct e; simplify; subst; simplify; invert H0.
    - econstructor. eapply StkStep_Const. eauto with instrs.
      econstructor.
    - econstructor. eapply StkStep_LoadVar. eauto with instrs.
      econstructor.
    - autorewrite with instrs.
      eapply trc_trans. apply IHe. auto. constructor. auto. stk_step_fold_one.
      econstructor. eapply StkStep_Unary. eauto with instrs.
      autorewrite with instrs. econstructor.
    - autorewrite with instrs.
      eapply trc_trans. apply IHe1. auto. constructor; auto. stk_step_fold_one.
      eapply trc_trans. apply IHe2. auto. instr_at_auto. stk_step_fold_one.
      econstructor. apply StkStep_Binary. eauto with instrs.
      autorewrite with instrs. econstructor.
  Qed.

  (*
    For compiler correctness, let's to prove simulation relation.

    We're proving simulation against CPS semantics than usual small-step semantics.
    Because while expansion is not local for small-step semantics.

    Support we have
      (va, While be body)     ~~>         (va, Seq body (While be body))
    and
      (va, While be body)     ~[instrs]~  (pc, va, nil)
    The Seq here is different from other Seq's in the sense that it's jumping backwards.
    So we cannot really relate    Seq c1 c2   with   compile c1 ++ compile c2 .

TODO: What if we do like
  Relate_RealSeq:
    instrs_at instrs pc (compile c1) ->
    instrs_at instrs (pc + | compile c1 |) (compile c2)
    relate_step instrs (va, Seq c1 c2) (pc, va, nil)

  Relate_WhileExpandedSeq:
    instrs_at instrs pc (compile body) ->
    instrs_at instrs (pc + | compile body |) [ UncondJumpBw | compile (While..)| ] ->
    instrs_at instrs (pc - | compile (While..) |) (compile (While be body)) ->
            (* watch out for underflow *)
    relate_step instrs (va, Seq body (While be body)) (pc, va, nil)

  we can imagine inversion will be painful cause we cannot tell the difference.
  why this is not a problem in CPS? because we syntactically make a Cont_While difference.
  (* TODO: elaborate *)

    Similar issues in CPS are addressed by cont_at
      which is basically a cont relate function.
    *)

  Import Small_cps.
  Open Scope nat.

  (* Effect of executing all the way from `pc` is same as executing the continuation. *)
  Inductive cont_at (instrs : list stack_instr) : nat -> Cont -> Prop :=
  | MkContAt_Cont_Stop: forall pc,
    instr_at instrs pc StkHalt ->
    cont_at instrs pc Cont_Stop
  | MkContAt_Cont_Seq: forall pc c k cinstrs,
    cinstrs = compile_cmd_to_stk c ->
    instrs_at instrs pc cinstrs ->
    cont_at instrs (pc + length cinstrs) k ->
    cont_at instrs pc (Cont_Seq c k)
  | MkContAt_Cont_While: forall pc be body k offset whileinstrs,
    whileinstrs = compile_cmd_to_stk (While be body) ->
    instrs_at instrs pc [ StkConst 1 ] ->
    instrs_at instrs (pc + 1) [ StkCondJumpBw offset ] ->
    instrs_at instrs (pc + 1 - offset) whileinstrs ->
    cont_at instrs (pc + 1 - offset + length whileinstrs) k ->
    cont_at instrs pc (Cont_While be body k)
  (* Without MkContAt_Jump we cannot prove simulation for If *)
  | MkContAt_Jump: forall pc k bwdir offset,
    instrs_at instrs pc [ StkConst 1 ] ->
    instrs_at instrs (pc + 1) [ StkCondJump bwdir offset ] ->  (* this phrasing makes automation easier *)
    cont_at instrs (condgoto_dst 1 bwdir offset (pc + 1)) k ->
    cont_at instrs pc k.

  (* Since one step of cps incorporates many steps of stk e.g. expr evaluation,
     we do not relate the intermediate steps; thus estk is nil.

      cps ----------------------------------> cps'
       ~                                       ~
      stk --> stk0 --> stk1 --> ... --------> stk'
   *)
  Inductive relate_cps_stk (instrs : list stack_instr) : cps_state -> stk_state -> Prop :=
  | MkRelateCpsStk: forall va c k pc vstk cinstrs,
    va = vstk ->
    cinstrs = compile_cmd_to_stk c ->
    instrs_at instrs pc cinstrs ->
    cont_at instrs (pc + length cinstrs) k ->
    relate_cps_stk instrs (va, c, k) (pc, vstk, nil).

  Hint Constructors instr_at instrs_at : instrs.

  Lemma instr_len_single: forall instr : stack_instr, 1 = length [ instr ].
  Proof. cbv; auto. Qed.

  (* Thank compilerverif for the auto and autorewrite *)
  Hint Resolve instr_at_ibefore_2  : instrsx.

  Arguments Nat.add: simpl never.

  Lemma instrs_at_instr_at: forall instrs instr pc,
    instrs_at instrs pc [ instr ] -> instr_at instrs pc instr.
  Proof.
    intros. invert H. auto with instrs.
  Qed.

  (* See stepwise refinement proof before looking the following lemma and explanations.

     Since we've introduced a MkContAt_Jump ...
   *)
  Lemma cont_at_seq_norm: forall instrs pc c k vstk,
    cont_at instrs pc (Cont_Seq c k) ->
    exists pc',
      (stk_step instrs)^* (pc, vstk, nil) (pc', vstk, nil) /\
      instrs_at instrs pc' (compile_cmd_to_stk c) /\
      cont_at instrs (pc' + length (compile_cmd_to_stk c)) k.
  Proof.
    induct 1; simplify.
    - exists pc. split. apply TrcRefl. split; auto.
    - destruct IHcont_at as (pc' & Hstep & Hic).
      exists pc'; split; auto.
      eapply trc_trans; [|eapply Hstep].
      econstructor. eapply StkStep_Const. eauto using instrs_at_instr_at.
      econstructor. eapply StkStep_CondJump. eauto using instrs_at_instr_at.
      econstructor.
  Qed.

  Lemma cont_at_while_norm: forall instrs pc be body k vstk,
    cont_at instrs pc (Cont_While be body k) ->
    exists pc',
      (stk_step instrs)^* (pc, vstk, nil) (pc', vstk, nil) /\
      instrs_at instrs pc' (compile_cmd_to_stk (While be body)) /\
      cont_at instrs (pc' + length (compile_cmd_to_stk (While be body))) k.
  Proof.
    induct 1; simplify.
    - clear IHcont_at. invert H2.
      exists (length ibefore). (* note I cannot write  pc-offset  here because possible nat underflow *)
      split. autorewrite with instrs in *.
      eapply TrcFront. eapply StkStep_Const. apply instrs_at_instr_at. eassumption.
      eapply TrcFront. eapply StkStep_CondJump. apply instrs_at_instr_at. eassumption.
      unfold condgoto_dst. simplify. rewrite H. apply TrcRefl.
      split. auto with instrs. rewrite H. assumption.
    - destruct IHcont_at as (pc' & Hstep & Hic).
      exists pc'; split; auto.
      eapply trc_trans; [|eapply Hstep].
      econstructor. eapply StkStep_Const. eauto using instrs_at_instr_at.
      econstructor. eapply StkStep_CondJump. eauto using instrs_at_instr_at.
      econstructor.
  Qed.

(* TODO: clarify difference between instr_at_auto and auto with instrs *)

  (*
   * Key theorem to compiler-correctness.
   *)
  Lemma stepwise_refinement_cps_stk: forall instrs cs ss,
    relate_cps_stk instrs cs ss ->
    forall cs',
      cps_step cs cs' ->
      exists ss',
        (stk_step instrs)^* ss ss' /\ relate_cps_stk instrs cs' ss'.
  Proof.
    invert 2; invert H.
    - (* computation of Assign *)
      simplify. invert H6. autorewrite with instrs in *.
      eexists.
      split.
      + (* next stk state: pc+1, vstk', estk *)
        eapply trc_trans.
        apply compile_exp_ok; auto with instrs.
        eapply TrcFront. apply StkStep_StoreVar. auto with instrs.
        econstructor.
      + (* relate *)
        econstructor; auto.
        instr_at_auto.
        autorewrite with instrs in *. auto.
    - (* computation of If *)
      simplify. invert H6. autorewrite with instrs in *.
      (* since then / else clauses have different next states, need to eexists early *)
      cases (value_to_bool (eval_exp vstk be)); eexists.
      + split. (* then *)
        * (* next stk state: after execute condgoto *)
          eapply trc_trans. apply compile_exp_ok; auto with instrs.
          eapply TrcFront. eapply StkStep_CondJump; apply instr_at_ibefore_2. (* why cannot do auto here? *)
          unfold condgoto_dst; rewrite Heq.
          apply TrcRefl.
        * (* relate *)
          econstructor; auto.
          instr_at_auto.
          autorewrite with instrs in *. assumption.
      + split. (* else *)
        * (* next stk state: after execute condgoto *)
          eapply trc_trans. apply compile_exp_ok; auto with instrs.
          eapply TrcFront. eapply StkStep_CondJump; apply instr_at_ibefore_2.
          unfold condgoto_dst; rewrite Heq.
          apply TrcRefl.
        * (* relate *)
          econstructor; auto.
          instr_at_auto.
          eapply MkContAt_Jump. instr_at_auto. instr_at_auto.
          unfold condgoto_dst; simplify.
          autorewrite with instrs in *. assumption.
    - (* computation of while-false *)
      simplify. invert H7.
      autorewrite with instrs in *.
      eexists. split.
      * (* nest stk state: pc+lencode(while..), vstk, estk *)
        eapply trc_trans. apply compile_exp_ok; auto with instrs.
        eapply TrcFront. eapply StkStep_Unary; auto with instrs.
        eapply TrcFront. eapply StkStep_CondJump; apply instr_at_ibefore_3.
        unfold condgoto_dst. simplify. rewrite H1. simplify.
        apply TrcRefl.
      * (* relate *)
        econstructor; auto.
        instr_at_auto.
        autorewrite with instrs in *. assumption.
    - (* computation for assert *)
      simplify. invert H7.
      autorewrite with instrs in *.
      eexists. split.
      * (* next stk state: after skipped unreachable *)
        eapply trc_trans. apply compile_exp_ok; auto with instrs.
        eapply TrcFront. eapply StkStep_CondJump; apply instr_at_ibefore_2.
        unfold condgoto_dst. simplify. rewrite H1. simplify.
        apply TrcRefl.
      * (* relate *)
        econstructor; auto.
        instr_at_auto.
        autorewrite with instrs in *. assumption.
    - (* resumption for cont_seq *)
      simplify. invert H6.
      autorewrite with instrs in *.
      apply cont_at_seq_norm with (vstk := vstk) in H7.
      destruct H7 as (pc' & Hstep & Hiat & Hcat).
      eexists. split.
      + apply Hstep.
      + econstructor; auto.
    - (* resumption for while *)
      simplify. invert H6.
      autorewrite with instrs in *.
      apply cont_at_while_norm with (vstk := vstk) in H7.
      destruct H7 as (pc' & Hstep & Hiat & Hcat).
      eexists. split.
      + apply Hstep.
      + econstructor; auto.
    - (* focusing for seq *)
      simplify. invert H6.
      autorewrite with instrs in *.
      eexists. split.
      + apply TrcRefl.
      + econstructor; auto.
        instr_at_auto.
        econstructor; auto. instr_at_auto.
        autorewrite with instrs in *. assumption.
    - (* focusing for while *)
      simplify. invert H7.
      eexists. split.
      + (* after going into body *)
        autorewrite with instrs in *.
        eapply trc_trans. apply compile_exp_ok; auto with instrs.
        eapply TrcFront. eapply StkStep_Unary; auto with instrs.
        eapply TrcFront. eapply StkStep_CondJump; eapply instr_at_ibefore_3.
        unfold condgoto_dst. simplify. rewrite H1. simplify.
        apply TrcRefl.
      + econstructor; auto.
        { autorewrite with instrs in *. instr_at_auto. }
        econstructor; auto.
        { autorewrite with instrs in *. instr_at_auto. }
        { autorewrite with instrs in *. instr_at_auto. }
        instr_at_auto. lia. autorewrite with instrs in *. simplify.
        repeat rewrite app_length. simplify.

(* WTF this *)
        replace
          (Datatypes.length ibefore + (Datatypes.length (compile_exp_to_stk be) + (1 + (1 + (Datatypes.length (compile_cmd_to_stk body) + 1)))) - (1 + (Datatypes.length (compile_cmd_to_stk body) + (1 + (1 + Datatypes.length (compile_exp_to_stk be))))) + (Datatypes.length (compile_exp_to_stk be) + (1 + (1 + (Datatypes.length (compile_cmd_to_stk body) + (1 + 1))))))
        with
          (Datatypes.length ibefore + (Datatypes.length (compile_exp_to_stk be) + (1 + (1 + (Datatypes.length (compile_cmd_to_stk body) + (1 + 1))))))
        by lia.

        assumption.
  Qed.
End Stack_machine.

Module Unused.
  (* example: how to do fmap normalization *)
  Goal forall va,
    ((va $+ ("n", 2) $+ ("x", va $! "x" + 2) $+ ("n", 1)) = (va $+ ("n", 1) $+ ("x", va $! "x" + 2))).
  intros. maps_equal. Qed.

  Goal (forall x, x <> 5 -> (match x with | 5 => true | _ => false end) = false)%nat.
  (* any cleverer methods? *)
  repeat (destruct x; auto). intuition.
  Qed.

  Goal (forall x, x <> 5 -> (match x with | 5 => true | _ => false end) = false)%Z.
  (* any cleverer methods? *)
  destruct x; auto. (* how to cope with this ??? *)
  repeat (destruct p; auto).
  lia.
  Qed.

  (* when next_instrs_match was not defined like
      Definition next_instrs_match (s : stk_state) (c : list stack_instr) : Prop :=
        match s with
        | (pc, instrs, vstk, estk) =>
          sublist pc (pc + length c) instrs = c
        end.
     this module is required *)
  Module ShouldBeInCoqStd.
  Definition sublist (from to : nat) {A : Set} (l : list A) : list A :=
    firstn (to - from)%nat (skipn from l).

  (* there is firstn_firstn but no skipn_skipn. *)
  Lemma skipn_skipn: forall a b {A : Set} (l : list A),
    skipn a (skipn b l) = skipn (a+b) l.
  Proof.
    induct b; simplify.
    replace (a+0)%nat with a by lia; auto.
    cases l. repeat rewrite skipn_nil; auto.
    replace (a + S b)%nat with (S (a + b))%nat by lia.
    simplify. apply IHb.
  Qed.

  Lemma sublist_correct: forall from to {A : Set} (l : list A),
    (from < to)%nat ->
    l = firstn from l ++ sublist from to l ++ skipn to l.
  Proof.
    intros. unfold sublist.
    rewrite <- (firstn_skipn from l) at 1. f_equal.
    rewrite <- (firstn_skipn (to - from) (skipn from l)) at 1. f_equal.
    rewrite skipn_skipn. replace (to - from + from)%nat with to by lia. auto.
  Qed.

  Lemma sublist_nonempty: forall from len {A : Set} (l : list A),
    length (sublist from (from + len)%nat l) = len ->
    (from + len <= length l)%nat.
  Proof.
    unfold sublist; simplify.
    replace (from + len - from)%nat with len in * by lia.
    assert (length (skipn from l) >= len)%nat. admit. admit.
  Abort.
  End ShouldBeInCoqStd.
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
      invert H. invert H0. cases (value_to_bool (eval_exp va0 be)).
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
            We want to prove      (va0, body, Cont_While be body k0) ~>* (?va1, Skip, k0)
            But we have by IH     (va0, body, Cont_While be body k0) ~>* ( va1, Skip, Cont_While be body k0)
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
