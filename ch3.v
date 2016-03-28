Load utils. Import TAPL_Utils.
Load set. Import TAPL_Set NatSet.

From mathcomp Require Import ssreflect eqtype ssrbool.
Require Import List Omega.
Require Import Classical_Prop Classical_Pred_Type.
Require Import Wf_nat.
Import ListNotations.

Module TAPL_Chapter_3.

Module Arith.

Inductive term :=
| Strue : term
| Sfalse : term
| Sif : term -> term -> term -> term
| S0 : term
| Ssucc : term -> term
| Spred : term -> term
| Siszero : term -> term.

Scheme Equality for term.

Module TermMDT <: MiniDecidableType.
  Definition t := term.
  Definition eq_dec := term_eq_dec.
End TermMDT.

Module TermDT := Make_UDT TermMDT.
Module TermSet := MSetWeakList.Make TermDT.
Module TermSetExt := SetExt TermDT TermSet.

Notation term_set := TermSet.t.
Import TermSetExt TermSetExt.Notations.

Local Open Scope set_scope.

Check {{0}}%nat_set.
Check {{Strue}}.

Fixpoint const (t : term) : term_set :=
  match t with
      Strue => {{ Strue }}
    | Sfalse => {{ Sfalse }}
    | S0 => {{ S0 }}
    | Ssucc t1 => const t1
    | Spred t1 => const t1
    | Siszero t1 => const t1
    | (Sif t1 t2 t3) => (const t1) \/ (const t2) \/ (const t3)
  end.

Fixpoint size (t : term) : nat :=
  match t with
      Strue => 1
    | Sfalse => 1
    | S0 => 1
    | Ssucc t1 => (size t1) + 1
    | Spred t1 => (size t1) + 1
    | Siszero t1 => (size t1) + 1
    | (Sif t1 t2 t3) => (size t1) + (size t2) + (size t3) + 1
  end.

Fixpoint depth (t : term) : nat :=
  match t with
      Strue => 1
    | Sfalse => 1
    | S0 => 1
    | Ssucc t1 => (depth t1) + 1
    | Spred t1 => (depth t1) + 1
    | Siszero t1 => (depth t1) + 1
    | (Sif t1 t2 t3) => max_l [(depth t1); (depth t2); (depth t3)] + 1
  end.

Lemma lem_3_3_3 : forall (t : term), #(const t) <= size t.
Proof.
  move=> t.
  elim t => //=.
  + move=> t1 IH1 t2 IH2 t3 IH3.
    have H1 := cardinal_union (const t2) (const t3).
    have H2 := cardinal_union (const t1) ((const t2) \/ (const t3)).
    omega.
  + move=> t'; omega.
  + move=> t'; omega.
  + move=> t'; omega.
Qed.

Theorem thm_3_3_4_depth (P : term -> Prop) :
  (forall s, (forall r, depth r < depth s -> P r) -> P s) -> forall s, P s.
Proof. exact (induction_ltof1 term depth P). Qed.

Theorem thm_3_3_4_size (P : term -> Prop) :
  (forall s, (forall r, size r < size s -> P r) -> P s) -> forall s, P s.
Proof. exact (induction_ltof1 term size P). Qed.

Definition thm_3_3_4_struct := term_ind.

End Arith.

Module Bool.

Inductive term : Set :=
| Strue : term
| Sfalse : term
| Sif : term -> term -> term -> term.

Scheme Equality for term.

Lemma term_beqP : Equality.axiom term_beq.
Proof.
  move=> n m. apply: (iffP idP) => [|<-]; last first.

  - elim n => //. move=> t1 IH1 t2 IH2 t3 IH3.
    simpl.
      by rewrite IH1 IH2 IH3.
  - move: m; elim n => //; try by move=>m; elim m => //.
    + move=> t1 IH1 t2 IH2 t3 IH3 m.
      case m => //.
      move=> t1' t2' t3'.
      move/andP => [] H1 /andP [] H2 H3.
      by rewrite (IH1 t1' H1) (IH2 t2' H2) (IH3 t3' H3).
Qed.

Canonical term_eqMixin := EqMixin term_beqP.
Canonical term_eqType := Eval hnf in EqType term term_eqMixin.

Implicit Arguments term_beqP [x y].
Prenex Implicits term_beqP.

Inductive value : term -> Prop :=
| Vtrue : value Strue
| Vfalse : value Sfalse.

Hint Constructors value.

Inductive eval : term -> term -> Prop :=
| EIfTrue t2 t3 : eval (Sif Strue t2 t3) t2
| EIfFalse t2 t3 : eval (Sif Sfalse t2 t3) t3
| EIf t1 t1' t2 t3 : eval t1 t1' -> eval (Sif t1 t2 t3) (Sif t1' t2 t3).

Hint Constructors eval.

Lemma eval_if : forall t1 t2 t3, exists t', eval (Sif t1 t2 t3) t'.
Proof.
  clear. move=> t1.
  elim t1=> [t2 t3|t2 t3|].
  - by exists t2.
  - by exists t3.
  - move=> t11 IH1 t12 IH2 t13 IH3 t2 t3.
    have := (IH1 t12 t13) => [[t1' M]].
    exists (Sif t1' t2 t3).
      by apply EIf.
Qed.

Lemma eval_value : forall t {t'}, value t -> eval t t' -> False.
Proof.
  move=> t t' H.
  inversion H => H1; inversion H1.
Qed.

Theorem eval_conv : forall t t' t'', eval t t' -> eval t t'' -> t' = t''.
Proof.
  move=> t.
  elim t; try by move=> t' t'' H; inversion H => //.

  move=> t1 IH1 t2 IH2 t3 IH3.
  move=> t' t'' H1 H2.

  case_eq t1.
  + move=> E; rewrite E in H1, H2.
    inversion H1 => //; clear dependent t0; clear dependent t4.
    inversion H2 => //; clear dependent t0; clear dependent t4.
    by rewrite<- H4; rewrite<- H5.
      by inversion H6 => //.
        by inversion H5 => //.
  + move=> E; rewrite E in H1, H2.
    inversion H1 => //; clear dependent t0; clear dependent t4.
    inversion H2 => //; clear dependent t0; clear dependent t4.
    by rewrite<- H4; rewrite<- H5.
      by inversion H6 => //.
        by inversion H5 => //.
  + move=> t11 t12 t13 E. rewrite E in H1, H2.
      inversion H1 => //; clear dependent t0; clear dependent t4; clear dependent t5.
      inversion H2 => //; clear dependent t0; clear dependent t4; clear dependent t5.
      rename t1'0 into t1''.
      rewrite E in IH1.
      have IH1' := (IH1 t1' t1'').
      have : t1' = t1'' by auto.
      move=>M; rewrite M.
      done.
Qed.

Definition eval_inv_spec t t' (e:eval t t') : Prop :=
    match t with
      | Sif Strue t2 t3 => t' = t2
      | Sif Sfalse t2 t3 => t' = t3
      | Sif (Sif t11 t12 t13) t2 t3 => exists t1' (e' : eval (Sif t11 t12 t13) t1'),
                                         t' = Sif t1' t2 t3
      | _ => False
    end.

Lemma eval_inv : forall (t t' : term) (e:eval t t'), eval_inv_spec t t' e.
Proof.
  move=> t.
  elim t; try by move=> t' e; inversion e.

  move=> t1 IH1 t2 IH2 t3 IH3 t'.
  move=> e.
  rewrite/eval_inv_spec.
  case_eq t1 => [E|E|]; try subst.

  - inversion e; subst => //.
    inversion H3.
  - inversion e; subst => //.
    inversion H3.
  - move=> t11 t12 t13 E.

    rewrite E in IH1.
    unfold eval_inv_spec in IH1.

    have := (eval_if t11 t12 t13) => [[t1' e']].
    have IH1' := (IH1 t1' e'); clear IH1.
    exists t1'; exists e'.

    case_eq t11.
    + move=> E0; rewrite E0 in IH1'; subst.
      inversion e; subst => //.
      inversion e' => //; try by inversion H4.
      inversion H3; subst => //; try by inversion H7.
    + move=> E0; rewrite E0 in IH1'; subst.
      inversion e; subst => //.
      inversion e' => //; try by inversion H4.
      inversion H3; subst => //; try by inversion H7.
    + move=> t111 t112 t113 E0; rewrite E0 in IH1'; subst.
      inversion e; subst => //.
      rename t1'0 into t1''.
      have : t1'' = t1' by eauto using eval_conv.
      by move=> ->.
Qed.

Fixpoint eval1 (t : term) : option term :=
  match t with
      Sif Strue t2 _ => Some t2
    | Sif Sfalse _ t3 => Some t3
    | Sif t1 t2 t3 =>
      option_map (fun t1' => Sif t1' t2 t3) (eval1 t1)
    | _ => None
  end.

Lemma eval1_spec : forall t t', eval1 t = Some t' -> eval t t'.
Proof.
  move=> t.
  elim t => //= t1 IH1 t2 IH2 t3 IH3 t'.
  case_eq t1; try by move=> E H; injection H => H'; rewrite H'.

  move=> t11 t12 t13 E1.
  unfold option_map.
  rewrite<- E1.
  case_eq (eval1 t1); try by auto.
  move=> t1' E2 H.
  injection H => H'.
  rewrite<- H'.
  apply (EIf t1 _ t2 t3).
  by apply (IH1 _).
Qed.

Theorem thm_3_5_4 : forall t t' t'', eval t t' -> eval t t'' -> t' = t''.
Proof. exact eval_conv. Qed.

Definition normal (t : term) := ~ exists t', eval t t'.

Theorem thm_3_5_7 : forall t, value t -> normal t.
Proof.
  move=> t H.
  unfold normal.
  apply all_not_not_ex.
  move=> t' H1.
  inversion H;
    by rewrite<- H0 in H1; inversion H1.
Qed.

Theorem thm_3_5_8 : forall t, normal t -> value t.
Proof.
  move=> t nm.
  case_eq t; try by constructor.
  move=> t1 t2 t3 E.
  rewrite E in nm.
  suff : ~ (normal (Sif t1 t2 t3)) by contradiction.

  clear.
  unfold normal.
  have PPNN : forall P : Prop, P -> ~ ~ P by auto.
    apply PPNN; clear PPNN.
  move: t2 t3; elim t1.
  + move=> t2 t3; exists t2; by auto.
  + move=> t2 t3; exists t3; by auto.
  + move=> t11 IH1 t12 IH2 t13 IH3 t2 t3.
    have IH1' := (IH1 t12 t13).
    destruct IH1' as [t1' H].
    exists (Sif t1' t2 t3).
    by constructor.
Qed.

Inductive evalM : term -> term -> Set :=
| EMSingle t t' : eval t t' -> evalM t t'
| EMRefl t : evalM t t
| EMTrans t t' t'' : evalM t t' -> evalM t' t'' -> evalM t t''.

Hint Constructors evalM.

Fixpoint evalM_size {t t' : term} (e : evalM t t') {struct e} : nat :=
  match e with
      EMSingle _ _ _ => 1
    | EMRefl _ => 0
    | EMTrans _ _ _ e1 e2 => (evalM_size e1) + (evalM_size e2) + 1
  end.

Lemma evalM_size_ind : forall P, (forall t t' (e : evalM t t'), (forall t0 t'0 (d : evalM t0 t'0), evalM_size d < evalM_size e -> P t0 t'0 d) -> P t t' e) -> (forall (t t' : term) (e : evalM t t'), P t t' e).
Proof.
Admitted.

Definition evalM_eval {t t'} (E : t <> t') (e : evalM t t') : ({ s : term & (eval t s) * (evalM s t')})%type.
  induction e => //; subst; rename t0 into t.
  - apply (existT _ t'). by apply pair.
  - case (term_eq_dec t t') => E0; subst.
    + by apply IHe2 in E.
    + apply IHe1 in E0.
      destruct E0 as [s [H11 H12]].
      apply (existT _ s); apply pair => //.
      by apply (EMTrans s t').
Defined.

Definition evalM_eval2 {t t'} (E : t <> t') (e : evalM t t') : ({ s : term  & { em : evalM s t' & (eval t s) * (evalM_size em < evalM_size e)} })%type.
  induction e => //; subst; rename t0 into t.
  - apply (existT _ t').
    apply (existT _ (EMRefl t')).
    by apply pair.
  - case (term_eq_dec t t') => E0; subst.
    + move: (IHe2 E) => [s [em [H1 H2]]].
      apply (existT _ s).
      apply (existT _ em).
      by apply pair => //; simpl; omega.
    + move: (IHe1 E0) => [s [em [H1 H2]]].
      apply (existT _ s).
      apply (existT _ (EMTrans s t' t'' em e2)).
      by apply pair => //; simpl; omega.
Defined.

Lemma evalM_value : forall t t', value t -> evalM t t' -> t = t'.
Proof.
  move=> t t' H1 H2; move: H2 H1.
  elim; clear t t'.
  - move=> t t' Ha Hb.
    inversion Hb; subst; inversion Ha.
  - done.
  - move=> t t' t''.
    move=> H1 IH1 H2 IH2 H.
    have IH1' := (IH1 H).
    have H' := H; rewrite IH1' in H'.
    have IH2' := (IH2 H').
    by rewrite IH1'.
Qed.

Inductive evalN : term -> term -> Set :=
| ENSingle t t' : eval t t' -> evalN t t'
| ENRefl t : evalN t t
| ENTrans t t' t'' : eval t t' -> evalN t' t'' -> evalN t t''.

Hint Constructors evalN.

Derive Inversion evalN_inv with (forall t t' : term, evalN t t') Sort Set.

Definition iffT (A B : Type) := ((A -> B) * (B -> A))%type.
Notation "A <--> B" := (iffT A B) (at level 95).

Lemma evalN_spec : forall t t', evalM t t' <--> evalN t t'.
Proof.
  move=> t t'.
  rewrite/iffT; constructor => H.
  (* -> *)
  induction H using evalM_size_ind; try rename t0 into t.
  destruct H; try rename t0 into t; try eauto using ENSingle, ENRefl.
  destruct (term_eq_dec t t'); subst.
  apply (H0 _ _ H1); by simpl; omega .
  destruct (evalM_eval2 n H) as [s [em [H2 H3]]].
  suff : evalN s t'' by eauto using ENTrans.
  apply( H0 _ _ (EMTrans _ _ _ em H1)).
  by intros; simpl; omega.

  (* <- *)
  elim H; intros; subst; try eauto using EMSingle, EMRefl.
Qed.

Lemma false_fancy : forall {P} (p : P -> False), forall Q, P -> Q.
Proof. by intros; elimtype False. Qed.

Theorem thm_3_5_11 :
  forall t u u', normal u -> normal u' -> evalM t u -> evalM t u' -> u = u'.
Proof.
  set lemA := thm_3_5_8.
  have lemB : forall t {t'}, normal t -> eval t t' -> False; eauto using thm_3_5_8, eval_value.

  move=> t u u' Hn Hn' He He'.
  apply evalN_spec in He; apply evalN_spec in He'.

  induction He; induction He'; subst; try rename t0 into t => //.
  - eauto using eval_conv.
  - apply lemA in Hn'.
    inversion Hn' as [E|E]; rewrite<- E in e; inversion e.
  - have : t' = t'0 by eauto using eval_conv. intros; subst t'0.
    apply lemA in Hn.
    inversion Hn as [E|E]; subst t'; idtac
    ; inversion He'; subst => //; inversion H.
  - elim (lemB t t') => //.
  - elim (lemB t t') => //.
  - move: (eval_conv _ _ _ e e0); intros; subst t'0.
    apply IHHe => //.
  - elim (lemB t t') => //.
  - move: (eval_conv _ _ _ e e0); intros; subst t'0.
    apply IHHe => //.
Qed.

End Bool.

End TAPL_Chapter_3.
