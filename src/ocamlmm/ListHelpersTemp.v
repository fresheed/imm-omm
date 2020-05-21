(******************************************************************************)
(** The following lemmas are proved in Coq 8.10 **)
(******************************************************************************)
Require Import List.

Lemma skipn_app n : forall {A: Type} (l1 l2: list A),
    skipn n (l1 ++ l2) = (skipn n l1) ++ (skipn (n - length l1) l2).
Proof. Admitted.

Lemma skipn_firstn_comm : forall {A: Type} m n (l: list A),
    skipn m (firstn n l) = firstn (n - m) (skipn m l).
Proof. Admitted.

Lemma firstn_skipn_comm : forall {A: Type} m n (l: list A),
    firstn m (skipn n l) = skipn n (firstn (n + m) l).
Proof. Admitted. 
