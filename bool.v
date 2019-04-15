Inductive bool : Type :=
  | true
  | false.

Definition negb(b:bool) : bool :=
match b with
| true => false
| false => true
end.

Example test_neg : (negb true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Notation "x && y" := (andb x y).

Compute (andb true true).
Compute (true && false).

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => (negb b2)
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.


