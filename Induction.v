Require Export Basics.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n', assume n' * 0 = 0 *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

(*
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.
*)

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
    intros n m. induction n as [| n' IHn'].
    - (* n = 0 *)
      reflexivity.
    - (* n = S n', assume S (n' + m) = n' + (S m) *)
      simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
    intros n m. induction n as [| n' IHn'].
    - (* n = 0 *)
      rewrite <- plus_n_O.
      reflexivity.
    - (* n = S n', assume n'+m = m+n' *)
      simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n', assume n'+(m+p) = (n'+m)+p *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.


Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - (* n = S n', assume double n' = n' + n' *)
    (* double S n' = S (S (double n')) = S (S (n' + n')) == S (n' + S n') *)
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.
















(* END OF FILE*)
