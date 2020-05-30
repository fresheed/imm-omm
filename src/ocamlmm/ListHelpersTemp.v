(******************************************************************************)
(** The following lemmas are proved in Coq 8.10 **)
(** Proofs have been (partially) copied from it **)
(******************************************************************************)
Require Import List.
From hahn Require Import Hahn.

Variable A : Type.

Lemma skipn_firstn_comm : forall m n (l: list A),
    skipn m (firstn n l) = firstn (n - m) (skipn m l).
Proof.
  now induction m; intros [] []; simpl; rewrite ?firstn_nil.
Qed.


Lemma firstn_skipn_comm : forall m n (l: list A),
  firstn m (skipn n l) = skipn n (firstn (n + m) l).
Proof.
  now intros m; induction n; intros []; simpl; destruct m.
Qed.

Lemma skipn_app n : forall {A: Type} (l1 l2: list A),
    skipn n (l1 ++ l2) = (skipn n l1) ++ (skipn (n - length l1) l2).
Proof.
  induction n; auto; intros.
  destruct l1; auto.
  rewrite <- app_comm_cons. simpl.
  auto.
Qed.  