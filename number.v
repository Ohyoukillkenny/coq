(* Module NatPlayground.
Inductive nat : Type :=
  | O
  | S (n : nat).

Inductive nat' : Type :=
  | stop
  | tick (foo : nat').

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.
End NatPlayground.*)
Inductive bool : Type :=
  | true
  | false.

Definition negb(b:bool) : bool :=
match b with
| true => false
| false => true
end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Notation "x && y" := (andb x y).


Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n: nat) (m :nat) : nat :=
  match n with
    | 0 => 0
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

(*Compute (mult 3 2).*)

Fixpoint factorial (n:nat) : nat:=
  match n with
    | 0 => 1
    | S n' => mult n (factorial n')
  end.

(* Compute (factorial 3).*)

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Definition ltb (n m: nat) : bool:=
  ((leb n m) && (negb (eqb n m))).


Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m -> 
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  rewrite -> H1.
  intros H2.
  rewrite -> H2. 
  reflexivity.
  Qed.





























