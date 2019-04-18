Require Export Induction.
Require Export Basic.
Module NatList.

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.


(* 
unlike its behavior with nats, where it generates two subgoals, 
destruct generates just one subgoal here. 
That's because natprods can only be constructed in one way.
 *)
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

(* higher level, lower previledge *)
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat := 
  match l with
  | nil => 0
  | h :: t => S (length t)
  end.

(* nil of the first list will be skipped *)
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default : nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => (nonzeros t)
  | h :: t => h :: (nonzeros t) 
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist := 
  match l with
  | nil => nil
  | h :: t => match oddb h with
              | true => h :: (oddmembers t)
              | false => oddmembers t
              end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  (length (oddmembers l)).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
reflexivity. Qed.  

Example test_countoddmembers3:
  countoddmembers nil = 0.
reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1 :: t1 => match l2 with
              | nil => h1 :: t1
              | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
              end
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
reflexivity. Qed.


Definition bag := natlist.

Fixpoint eqb (x y:nat) : bool :=
  match x with
  | 0 => match y with
         | 0 => true
         | S y' => false
         end
  | S x' => match y with
            | 0 => false
            | S y' => (eqb x' y')
            end
  end.
Notation " x =? y" := (eqb x y) (at level 70) : nat_scope.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t => match h =? v with
              | true => S (count v t)
              | false => (count v t)
              end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
reflexivity. Qed.

(* interesting! *)
Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
reflexivity. Qed.


Definition add (v:nat) (s:bag) : bag := v :: s.


Example test_add1: count 1 (add 1 [1;4;1]) = 3.
reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
reflexivity. Qed.


Definition member (v:nat) (s:bag) : bool:= (negb ((count v s) =? 0)).

Example test_member1: member 1 [1;4;1] = true.
reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
reflexivity. Qed.


Fixpoint remove_one (v:nat) (s:bag) : bag := 
  match 


Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* FILL IN HERE *) Admitted.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* FILL IN HERE *) Admitted.
Fixpoint subset (s1:bag) (s2:bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Example test_subset1: subset [1;2] [2;1;4;1] = true.
 (* FILL IN HERE *) Admitted.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
 (* FILL IN HERE *) Admitted.



















End NatList.

























