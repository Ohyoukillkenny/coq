(*
Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin := 
  match m with
  | Z => B Z
  | A m' => B m'
  | B m' => A (incr m')
  end.



Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => 0
  | A n' => 2 * (bin_to_nat n')
  | B n' => 1 + (2 * (bin_to_nat n'))
end.
*)

Inductive bin : Type :=
| BO : bin
| D : bin -> bin
| M : bin -> bin.

Fixpoint incbin (n : bin) : bin :=
match n with
| BO => M (BO)
| D n' => M n'
| M n' => D (incbin n')
end.

Fixpoint double (n:nat) :=
match n with
| O => O
| S n' => S (S (double n'))
end.

Fixpoint bin2un (n : bin) : nat :=
match n with
| BO => O
| D n' => double (bin2un n')
| M n' => S (double (bin2un n'))
end.

Theorem bin_comm : forall n : bin,
bin2un(incbin n) = S (bin2un n).
Proof.
  intros n.
  induction n.
  reflexivity.
  reflexivity.
  simpl.
  rewrite -> IHn.
  reflexivity.
Qed.




















