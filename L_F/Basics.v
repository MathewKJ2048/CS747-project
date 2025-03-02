

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_working_day (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

  Compute next_working_day friday.

Inductive bool : Type :=
| true
| false.

Definition negb(b: bool) : bool :=
match b with
| true => false
| false => true
end.

Example test_1: (negb true) = false.
Proof.
simpl.
reflexivity.
Qed.

Definition andb (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

Notation "x && y" := (andb x y).

(* when dealing with inductive types, first clause is treated as equivalent to true*)

Inductive ball : Type :=
| red'
| blue'.

Compute (if red' then 4 else 3).

Definition nandb (a:bool) (b:bool) : bool :=
if a then negb b else true.

Example test_nandb1: (nandb true false) = true.
Proof.
unfold nandb.
unfold negb.
reflexivity.
Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
if b1 then andb b2 b3 else false.

Example test_andb31: (andb3 true true true) = true.
Proof.
unfold andb3.
unfold andb.
reflexivity.
Qed.


Check true.

Check negb. (*function type*)

Check negb true.

Check andb.

(*enum - enumerated type - each in finite set of leements is called a constructor*)

Inductive rgb : Type :=
| red
| blue
| green.

Inductive color : Type :=
| black
| white
| primary (p:rgb).

(* constructors can be applied to other constructors, this is a constructor expression*)

Check primary.
Check red.
Check primary red.

Definition monochrome (c: color):bool:=
match c with
| primary p => false
| _ => true
end.

Compute monochrome black.
Compute monochrome (primary red).


Module Playground.
  Definition foo : rgb := blue.
End Playground.

Definition foo: bool := true.
Check Playground.foo.
Check foo.

(*Tuples 
single constructor with multiple parameters

*)

Inductive bit:Type:=
| B1
| B0.

Inductive nybble: Type:=
| bitbit (b1 b2 b3 b4: bit).

Check bitbit B1 B1 B1 B1.

(* underscore used as wildcard pattern*)

Definition is_zero(nb: nybble) : bool :=
match nb with
| bitbit B0 B0 B0 B0 => true
| bitbit _ _ _ _ => false
end.

Compute is_zero (bitbit B0 B0 B0 B0).

Module NatPlayground.

Inductive nat : Type:=
| O
| S (n : nat).

Compute O.
Compute S O.
Compute S (S O).

Fixpoint add(a b : nat) : nat :=
match a with
| S x => add (x) (S b)
| O => b
end.

Compute add (S (S O)) (S O).

Definition pred(n: nat): nat :=
match n with
| O => O
| S n' => n'
end.
End NatPlayground.

Check (S (S (S (S O)))).

Definition minusTwo (n: nat): nat:=
match n with
| O => O
| S O => O
| S ( S n') => n
end.

Compute minusTwo 4.

Fixpoint odd (n:nat): bool:=
match n with
| O => false
| S O => true
| S ( S n') => odd(n')
end.

Compute odd 5.

Example test_odd: odd 5 = true.
Proof.
simpl.
reflexivity.
Qed.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Example assoc_plus: forall n m: nat, plus n m = plus m n.
Proof.
Admitted.

Fixpoint product (n: nat) (m: nat) : nat :=
match n with
| O => O
| S n' => plus m (product n' m)
end.

Fixpoint minus(a b : nat): nat :=
match a, b with
| O , _ => O
| _ , O => a
| S x, S y => minus x y
end.

Fixpoint exp(a b : nat): nat :=
match b with
| O => S O
| S n => product a (exp a n)
end.

Fixpoint factorial(n: nat): nat :=
match n with
| O => S O
| S n' => product n (factorial n')
end.

Compute factorial 4.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof.
simpl.
reflexivity.
Qed.

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
| S n' => match m with
  | O => false
  | S m' => leb n' m'
end
end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb : 3<=?4 = true.
Proof.
simpl.
reflexivity.
Qed.

Definition ltb  (n m : nat) : bool :=
negb (leb m n).

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
intros.
reflexivity.
Qed.

(*
  keywords Example and Theorem (and a few others, including Lemma, Fact, and Remark) mean pretty much the same thing to Coq.
*)

Theorem plus_id_example: forall n m: nat, n = m -> n+n = m+m.
Proof.
intros n m.
intros H.
rewrite <- H.
reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
n = m -> m = o -> n+m = m+o.
Proof.
intros m n o.
intro H.
intro H2.
rewrite -> H.
rewrite H2.
reflexivity.
Qed.

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,
  mult p 0 + mult q 0 = 0.

Proof.
intros.
rewrite <- mult_n_O.
rewrite <- mult_n_O.
simpl.
reflexivity.
Qed.

Theorem mult_n_1 : forall p : nat, mult p 1 = p.
Proof.
intros.
rewrite <- mult_n_Sm.
rewrite <- mult_n_O.
simpl.
reflexivity.
Qed.

Print nat.

Theorem plus_1_neq_0_try :
forall n:nat,(n+1)=?0=false.
Proof.
intros.
destruct n as [| n'] eqn:E.
- simpl.
reflexivity.
- reflexivity.
Qed.

Theorem double_negation: forall b:bool, negb (negb b) = b.
Proof.
intros.
destruct b eqn:Eb.
reflexivity.
reflexivity.
Qed.

Theorem commutative_and: forall a b: bool, andb a b = andb b a.
Proof.
intros.
destruct a.
- simpl.
destruct b.
reflexivity.
reflexivity.
- simpl.
destruct b.
reflexivity.
reflexivity.
Qed.

Theorem and_assoc: forall a b c: bool, andb a (andb b c) = andb (andb a b) c.
Proof.
intros.
destruct a.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
intros.
destruct b.
simpl.
rewrite <- commutative_and.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intro b.
intro c.
destruct b.
destruct c as [].
intro.
reflexivity.
simpl.
intro.
rewrite <- H.
reflexivity.
destruct c as [|].
simpl.
intro.
reflexivity.
simpl.
intro.
rewrite <- H.
reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n:nat,
0 =? (n+1) = false.
Proof.
intros.
destruct n.
simpl.
reflexivity.
unfold eqb.
reflexivity.
Qed.

Theorem identity_fn_twice:
forall (f : bool -> bool), (forall (x:bool), f x = x) -> forall (b:bool), f ( f b) = b.
Proof.
intro f.
intro H.
destruct b.
rewrite <- H.
rewrite <- H.
reflexivity.
rewrite <- H.
rewrite <- H.
reflexivity.
Qed.

Theorem identity_fn_twic:
forall (f : bool -> bool), (forall (x:bool), f x = negb x) -> forall (b:bool), f ( f b) = b.
Proof.
intro f.
intro H.
destruct b.
rewrite -> H.
rewrite -> H.
simpl.
reflexivity.
rewrite -> H.
rewrite -> H.
reflexivity.
Qed.

Theorem andb_eq_orb:
forall (b c: bool), (andb b c = orb b c) -> b = c.
Proof.
intro b.
intro c.
destruct b.
simpl.
intro.
rewrite -> H.
reflexivity.
simpl.
intro.
rewrite -> H.
reflexivity.
Qed.

Module LateDays.

Inductive letter : Type :=
  | A | B | C | D | F.

Inductive modifier : Type :=
  | Plus | Natural | Minus.

Inductive grade : Type :=
  Grade (l:letter) (m:modifier).

Inductive comparison : Type :=
  | Eq (* "equal" *)
  | Lt (* "less than" *)
  | Gt. (* "greater than" *)

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

Check Grade.

Theorem sanity': forall l l':letter, l=l' -> letter_comparison l l' = Eq.
Proof.
intros.
rewrite <- H.
destruct l.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Qed.

Theorem letter_comparison_Eq: forall l :letter, letter_comparison l l = Eq.
Proof.
intro.
destruct l.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Qed.

Definition modifier_comparison(m1 m2:modifier): comparison :=
match m1, m2 with
| Plus, Plus => Eq
| Plus, _ => Gt
| Natural, Plus => Lt
| Natural, Natural => Eq
| Natural, _ => Gt
| Minus, (Plus | Natural) => Lt
| Minus, Minus => Eq
end.


Definition grade_comparison(g1 g2: grade): comparison :=
match g1, g2 with
| Grade l1 m1, Grade l2 m2 => 
match letter_comparison l1 l2 with
  | Eq => modifier_comparison m1 m2
  | c => c end
end.

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof.
reflexivity.
Qed.

Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof.
reflexivity.
Qed.

Definition lower_letter(l:letter): letter :=
match l with
| A => B
| B => C
| C => D
| _ => F
end.

Theorem lower_letter_lowers:
forall (l:letter),
letter_comparison F l = Lt ->
letter_comparison (lower_letter l) l = Lt.
Proof.
intro.
destruct l.
simpl.
intro.
reflexivity.
simpl.
intro.
reflexivity.
simpl.
intro.
reflexivity.
simpl.
intro.
reflexivity.
simpl.
intro.
rewrite <- H.
reflexivity.
Qed.



Definition lower_grade(g : grade) : grade :=
match g with
| Grade l m => match l, m with
  | F, Minus => Grade F Minus
  | g, Minus => Grade (lower_letter g) Plus
  | g, Plus => Grade g Natural
  | g, Natural => Grade g Minus
  end
end.

Compute lower_grade (Grade F Minus).


Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof.
simpl.
reflexivity.
Qed.

Check letter_comparison_Eq.


Theorem Natural_case: forall (l:letter), grade_comparison (lower_grade (Grade l Natural) ) (Grade l Natural)  = Lt.
Proof.
intro.
simpl.
destruct l.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Qed.

Theorem Plus_case: forall (l:letter), grade_comparison (lower_grade (Grade l Plus) ) (Grade l Plus) = Lt.
Proof.
intro.
simpl.
destruct l.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Qed.


Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
intro.
destruct g.
destruct m.
rewrite -> Plus_case.
reflexivity.
rewrite -> Natural_case.
reflexivity.
simpl.
destruct l.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
simpl.
intro.
rewrite <- H.
reflexivity.
Qed.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).


Theorem apply_late_policy_unfold :
  forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g)
    =
    (if late_days <? 9 then g else
       if late_days <? 17 then lower_grade g
       else if late_days <? 21 then lower_grade (lower_grade g)
            else lower_grade (lower_grade (lower_grade g))).
Proof.
  intros. reflexivity.
Qed.

Theorem no_penalty_for_mostly_on_time :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = true) ->
    apply_late_policy late_days g = g.
Proof.
intros.
unfold apply_late_policy.
rewrite -> H.
reflexivity.
Qed.

Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof.
intros.
unfold apply_late_policy.
rewrite -> H.
rewrite -> H0.
reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).


Fixpoint bin_to_nat (m: bin):nat :=
match m with
| B0 x => 2 * (bin_to_nat x)
| B1 x => 2 * (bin_to_nat x) + 1
| Z => 0
end.

Compute bin_to_nat (B0 (B1 Z)).

End LateDays.















