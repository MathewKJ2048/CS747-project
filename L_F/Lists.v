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


Check nat.


Search (rev).
Search (_ + _ = _ + _).

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
induction l.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros.
induction l1.
simpl.
rewrite app_nil_r.
reflexivity.
simpl.
rewrite IHl1.
rewrite app_assoc.
reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite rev_app_distr.
simpl.
rewrite IHl.
reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
induction l1.
simpl.
intros.
rewrite app_assoc.
reflexivity.
simpl.
intros.
rewrite IHl1.
reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
intros.
induction l1.
reflexivity.
simpl.
destruct n.
apply IHl1.
simpl.
rewrite IHl1.
reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
match l1, l2 with
| nil, nil => true
| x::la, y::lb => (eqb x y) && (eqblist la lb)
| _, _ => false
end.

Compute eqblist [1;2;3] [1;2].

Search (eqb _ _).

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite equality.
rewrite <- IHl.
reflexivity.
Qed.


Theorem plus_1_S: forall t, (t+1=S t).
Proof.
induction t.
    reflexivity.
    simpl.
    rewrite IHt.
    reflexivity.
    Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
assert (forall t, match t+1 with | 0 => false | S _ => true end = true).
{
  intros.
  rewrite plus_1_S.
  reflexivity.
}
intro.
simpl.
rewrite H.
reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
intros.
induction n.
reflexivity.
simpl.
apply IHn.
Qed.

Search (_ + 1).

Theorem add_zero: forall t, t+0=t.
Proof.
intros.
induction t.
reflexivity.
simpl.
rewrite IHt.
reflexivity.
Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
intros.
induction s.
reflexivity.
destruct n.
simpl.
rewrite plus_1_S.
rewrite leb_n_Sn.
reflexivity.
simpl.
rewrite -> add_zero.
rewrite -> add_zero.
apply IHs.
Qed.

Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
intros.
specialize (H n1) as H1.
specialize (H n2) as H2.
rewrite H1.
rewrite H2.
rewrite H0.
reflexivity.
Qed.

Search (rev (rev _)).

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
intros.
specialize (rev_involutive l1).
specialize (rev_involutive l2).
intros.
rewrite <- H0.
rewrite <- H1.
rewrite H.
reflexivity.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth (l:natlist) (n:nat) : natoption :=
match l with
| nil => None
| x::l' => match n with
  | 0 => Some x
  | S n' => nth l' n'
end
end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
match l with
| nil => None
| x::l' => (Some x)
end.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
intros.
induction l.
reflexivity.
simpl.
reflexivity.
Qed.

Inductive id : Type :=
  | Id (n : nat).



Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => (n1 =? n2)
  end.

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
intros.
destruct x.
simpl.
apply equality.
Qed.


Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x:id) (d:partial_map) : natoption :=
match d with
| empty => None
| record y v d' => 
  if (eqb_id x y) 
  then Some v 
  else find x d'
end.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> 
    find x (update d y o) = find x d.
Proof.
intros.
simpl.
rewrite H.
reflexivity.
Qed.

