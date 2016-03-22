Module TAPL_Utils.

From Ssreflect Require Import ssreflect.
Require Import Nat List Omega.
Import ListNotations.

Definition max_l (l : list nat) : nat := fold_left max l 0.

Lemma max_l_spec :
  forall (l : list nat) (x : nat), In x l -> x <= max_l l.
Proof.
  move=> l x.
  unfold max_l.
  elim l => // x' l' IH.
  simpl (fold_left _ _ _).

  simpl (In _ _); move=> [H | H].
  + suff L0 : forall l x x', x <= x' -> x <= fold_left max l x'.
    rewrite H; clear x' l H IH; rename l' into l.
    elim l => //; auto.

    clear=> l x.
    elim l => // x'' l' IH => /= x'.

    case (Max.max_spec x' x'').
    - move=> [H HR]. rewrite HR.
      move=> H1.
      apply (IH x''); omega.
    - move=> [H HR]. rewrite HR.
      apply (IH x').

  + apply IH in H.
    suff H1: (fold_left max l' 0) <= (fold_left max l' x') by omega.
    suff L1 : forall l x x', x <= x' -> fold_left max l x <= fold_left max l x'
      by apply (L1 l' 0 x' (le_0_n x')).
    clear=> l.
    elim l => // x'' l' IH => /= x x'.
    case (Max.max_spec x' x'').
    + move=> [H HR] H1.
      have H2 : x <= x'' by omega.
      rewrite HR.
      rewrite (Nat.max_r x x'' H2).
      done.
    + move=> [H HR] H1.
      apply (IH (max x x'') (max x' x'')).
      rewrite (Nat.max_l x' x'' H).
      apply Max.max_case_strong; intros; omega.
Qed.

End TAPL_Utils.
