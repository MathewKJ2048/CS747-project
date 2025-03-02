From LF Require Export Basics.

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.
Proof.
intros n.
induction n as [| n' IHn].
reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Theorem minus_n_n : forall n, minus n n = 0.
Proof.
intro n.
induction n as [| n' IHn].
reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Theorem mul_0_r: forall n:nat, n*0=0.
Proof.
intro n.
induction n as [| n' IHn].
reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros.
induction n as [|n'].
simpl.
reflexivity.
simpl.
rewrite -> IHn'.
reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros.
induction n.
simpl.
rewrite add_0_r_firsttry.
reflexivity.
simpl.
rewrite -> IHn.
rewrite plus_n_Sm.
reflexivity.
Qed.

Theorem add_assoc: forall n m p : nat, n+(m+p) = (n+m)+p.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n+n.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite -> IHn.
rewrite -> plus_n_Sm.
reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
intros.
induction n.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Fixpoint even (n:nat): bool:=
match n with
| O => true
| S O => false
| S ( S n') => even(n')
end.

Theorem even_S': forall n:nat, even (S n) = negb(even n).
Proof.
intros.
induction n.
reflexivity.
assert (forall x y: bool, y = negb x -> x = negb y).
intro x.
intro y.
destruct x.
simpl.
intro.
rewrite -> H.
reflexivity.
simpl.
intro.
rewrite -> H.
reflexivity.
specialize (H (even (n))).
specialize (H ((even (S n)))).
apply H in IHn.
rewrite <- IHn.
simpl.
reflexivity.
Qed.


Theorem even_S: forall n:nat, even (S n) = negb(even n).
Proof.
intros.
induction n.
reflexivity.
rewrite -> IHn.
simpl.
rewrite double_negation.
reflexivity.
Qed.

(*rewrite tactic searches from outside, matches outermost*)


Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros.
assert (H: n+(m+p) = (n+m)+p).
{ rewrite add_assoc. reflexivity. }
rewrite -> H.
assert (H2: n+m = m+n). 
{
	rewrite add_comm. reflexivity.
}
rewrite -> H2.
assert (H3: m+(n+p) = (m+n)+p).
{
	rewrite add_assoc. reflexivity.
}
rewrite H3.
reflexivity.
Qed.

Theorem helper : forall n k , n * S k = n + n*k.
Proof.
intros.
induction n.
reflexivity.
simpl.
rewrite IHn.
rewrite add_shuffle3.
reflexivity.
Qed.
(*
induction k.
assert (H1 : forall t , t*0 = 0).
intro.
induction t.
reflexivity.
simpl.
rewrite IHt.
reflexivity.
assert (H2: forall t, t*1=t).
intro.
induction t.
reflexivity.
simpl.
rewrite IHt.
reflexivity.
specialize (H1 n) as H1n.
specialize (H2 n) as H2n.
rewrite H1n.
rewrite H2n.
rewrite add_0_r_firsttry.
reflexivity.
*)


Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
induction n.
simpl.
induction m.
reflexivity.
simpl.
rewrite IHm.
reflexivity.
simpl.
rewrite <- IHn.
rewrite helper.
reflexivity.
Qed.

Check leb.
Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
intros.
induction p.
simpl.
rewrite H.
reflexivity.
simpl.
rewrite IHp.
reflexivity.
Qed.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
intros.
induction n.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
intros.
destruct b.
reflexivity.
reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
intros.
induction n.
reflexivity.
rewrite <- IHn.
simpl.
rewrite add_0_r_firsttry.
reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
intros.
destruct b.
simpl.
destruct c.
reflexivity.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
rewrite add_assoc.
reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite mult_plus_distr_r.
rewrite IHn.
reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros.
replace (n+(m+p)) with ((n+m)+p).
replace (m+(n+p)) with ((m+n)+p).
replace (n+m) with (m+n).
reflexivity.
rewrite add_comm.
reflexivity.
rewrite add_assoc.
reflexivity.
rewrite add_assoc.
reflexivity.
Qed.



