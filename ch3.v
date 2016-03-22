Module TAPL_Chapter_3.

Load utils. Import TAPL_Utils.
Load set. Import TAPL_Set NatSet.

From Ssreflect Require Import ssreflect.
Require Import List Omega.
Require Import Classical_Prop Classical_Pred_Type.
Require Import Wf_nat.
Import ListNotations.

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

Check {0}%nat_set.
Check {Strue}.

Fixpoint const (t : term) : term_set :=
  match t with
      Strue => { Strue }
    | Sfalse => { Sfalse }
    | S0 => { S0 }
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

Inductive value : term -> Prop :=
| Vtrue : value Strue
| Vfalse : value Sfalse.

Inductive eval : term -> term -> Prop :=
| EIfTrue t2 t3 : eval (Sif Strue t2 t3) t2
| EIfFalse t2 t3 : eval (Sif Sfalse t2 t3) t3
| EIf t1 t1' t2 t3 : eval t1 t1' -> eval (Sif t1 t2 t3) (Sif t1' t2 t3).

Hint Constructors eval.

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

Theorem thm_3_3_5 : forall t t' t'', eval t t' -> eval t t'' -> t' = t''.
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

Inductive evalM : term -> term -> Prop :=
| EMSingle t t' : eval t t' -> evalM t t'
| EMRefl t : evalM t t
| EMTrans t t' t'' : evalM t t' -> evalM t' t'' -> evalM t t''.

Theorem thm_3_5_11 :
  forall t u u', normal u -> normal u' -> evalM t u -> evalM t u' -> u = u'.
Proof.
Abort.

End Bool.

End TAPL_Chapter_3.
