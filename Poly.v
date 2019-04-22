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


Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(*
One good way to think about it is that list is a function 
from Types to Inductive definitions; or, to put it another 
way, list is a function from Types to Types. 
For any particular type X, the type list X is an Inductively 
defined set of lists whose elements are of type X.
*)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.
Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [|n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l as [| t l' IHl'].
  -reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.


Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1 as [| n l1' IHl1'].
  -reflexivity.
  -simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [| n l' IHl'].
  - rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl'.
    simpl. rewrite -> app_assoc. reflexivity.
Qed.



Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr.
    simpl. rewrite -> IHl'. reflexivity.
Qed.

(* Polymorphic Pairs *)

Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
  : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x,y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y))
  : (list X)*(list Y) :=
  match l with
  | [] => ([], [])
  | (x,y) :: l' => ( x::fst(split l'), y::snd(split l') )
  end.


Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.

Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | a :: _ => Some a
  end.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Fixpoint oddb (n:nat) : bool :=
  match n with
  | O        => false
  | S O      => true
  | S (S n') => oddb n'
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Notation " x && y " := (andb x y).

Fixpoint gt (x:nat) (y:nat) : bool :=
  match x with
  | 0 => false
  | S x' => match y with
            | 0 => true
            | S y' => (gt x' y')
            end
  end.

Fixpoint filter {X:Type} (test : X->bool) (l:list X) :
  (list X) :=
  match l with 
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => (evenb x) && (gt x 7)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Fixpoint partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                    : list X * list X :=
  match l with
  | [] => ([], [])
  | h :: t => if test h then (h :: fst(partition test t), snd(partition test t))
                        else (fst(partition test t), h :: snd(partition test t))
  end.


Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Lemma map_help : forall(X Y : Type) (f : X -> Y) (l : list X) (x : X),
  map f (l ++ [x]) = (map f l) ++ [f x].
Proof.
  intros X Y f l x. induction l as [| n l'].
  - reflexivity.
  - simpl.  rewrite -> IHl'. reflexivity.
Qed.


Theorem map_rev : forall(X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> map_help. 
    simpl. rewrite -> IHl'. reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.


Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (init: Y)
                         : Y :=
  match l with
  | nil => init
  | h :: t => f h (fold f t init)
  end.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof. 
intros X l. induction l as [| n l' IHl'].
-reflexivity.
-simpl. rewrite <- IHl'. reflexivity. 
Qed.

Fixpoint fold_map {X Y: Type} (f: X->Y) (l: list X)
                         : list Y :=
  match l with
  | nil => []
  | h :: t => (f h) :: (fold_map f t)
  end.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
intros X Y Z f.
reflexivity.
Qed.


Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
intros X Y Z f p. destruct p as [p1 p2].
reflexivity.
Qed.

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one : cnat := 
  fun (X : Type) (f : X->X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition succ (n : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. 
reflexivity.
Qed.

Example succ_2 : succ one = two.
Proof. reflexivity. Qed.

Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => m X f (n X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => (m X (n X f) x).

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

Definition exp (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => (m (X->X) (fun y => (fun z => (n X y z))) f) x.

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

















