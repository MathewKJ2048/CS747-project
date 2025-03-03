From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
intros.
reflexivity.
Qed.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. 
  destruct p as [n m]. 
  simpl. 
  reflexivity. 
  Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
intros.
destruct p as [a b].
reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
intros.
destruct p as [a b].
reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist): nat :=
match l with
| nil => 0
| x :: l' => S (length l')
end.

Fixpoint app (l1 l2 : natlist): natlist :=
match l1, l2 with
| nil, l => l
| x1::l, l' => x1::(app(l) (l'))
end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default: nat) (l:natlist) : nat :=
match l with
| nil => default
| h::t => h
end.

Definition tl (l:natlist) : natlist :=
match l with
| nil => nil
| h::t => t
end.

Fixpoint nonzeros (l:natlist) : natlist :=
match l with
| nil => nil
| 0::l' => nonzeros l'
| x::l' => x::(nonzeros l')
end.

Compute nonzeros [0;1;0;2;3;0;0].

Fixpoint oddmembers (l:natlist) : natlist :=
match l with
| nil => nil
| x::l' => if odd x then x::(oddmembers l') else l'
end.

Definition countoddmembers (l:natlist) : nat :=
length(oddmembers l).

Fixpoint alternate (l1 l2 : natlist) : natlist :=
match l1, l2 with
| nil, l => l
| l, nil => l
| x::l1', y::l2' => [x;y]++(alternate l1' l2')
end.

Compute alternate [1;2;3] [4;5;6].


Definition bag := natlist.

Fixpoint count (v: nat) (s: bag) : nat :=
match s with
| nil => 0
| x::l => (count v l) + (if eqb x v then 1 else 0)
end.

Definition sum : bag -> bag -> bag :=
app.

Compute count 1 (sum [1;2;3] [1;4;1]).

Definition add (v : nat) (s : bag) : bag :=
v::s.

Fixpoint member (v : nat) (s : bag) : bool :=
match s with
| nil => false
| x::l => orb (eqb x v) (member v l)
end.

Compute member 3 [1;4;1].

Fixpoint remove_one (v : nat) (s : bag) : bag :=
match s with
| nil => nil
| x::l => if eqb x v then l else x::(remove_one v l)
end.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
match s with
| nil => nil
| x::l => if eqb x v then (remove_all v l) else x::(remove_all v l)
end.

Compute count 5 (remove_one 5 [2;1;4;5;5;4]).


Fixpoint included (s1 : bag) (s2 : bag) : bool :=
match s1 with
| nil => true
| x::l => match (count x s2) with
  | 0 => false
  | _ => included (l) (remove_one x s2)
  end
end.

Example test_included2: included [1;2;2] [2;1;4;1] = false.

Theorem equality : forall n, eqb n n = true.
Proof.
intros.
induction n.
reflexivity.
simpl.
apply IHn.
Qed.

Theorem add_inc_count : forall (v:nat) (s:bag), count v (add v s) = count v s + 1.
Proof.
intros.
induction s.
simpl.
rewrite -> equality.
reflexivity.
simpl.
rewrite -> equality.
reflexivity.
Qed.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
intros.
destruct l.
reflexivity.
reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
intros.
induction l1.
reflexivity.
simpl.
rewrite IHl1.
reflexivity.
Qed.


Theorem repeat_plus: forall c1 c2 n: nat,
    repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
Proof.
intros.
induction c1.
reflexivity.
simpl.
rewrite IHc1.
reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
match l with
| nil => nil
| h::t => (rev t)++[h]
end.

Theorem length_dist: forall la lb, length(la++lb) = length la + length lb.
Proof.
intros.
induction la.
reflexivity.
simpl.
rewrite IHla.
reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite length_dist.
simpl.
rewrite IHl.
assert (forall n, n+1 = S n).
{
  intros.
  induction n0.
  reflexivity.
  simpl.
  rewrite IHn0.
  reflexivity.
}
rewrite H.
reflexivity.
Qed.







