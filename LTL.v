(*

Inductive prop : Type :=
| true
| false.

Check prop.

Definition and(p q:prop):prop :=
match p with
| false => false
| true => q
end.

Definition or(p q:prop):prop :=
match p with
| false => q
| true => true
end.

Definition not(p: prop):prop :=
match p with
| false => true
| true => false
end.

*)

(*
	basic operators
*)

Inductive LTL_formula : Type :=
| T
| P (n : nat)
| Or : LTL_formula -> LTL_formula -> LTL_formula
| Not : LTL_formula -> LTL_formula
| Next : LTL_formula -> LTL_formula
| Until : LTL_formula -> LTL_formula -> LTL_formula
.

Check (P 0).
Check (P 1).
Check (P 2).
Check (Or (P 0) (P 1)).
Check (Not (P 0)).

(*
	derived operators
*)

Definition And (f1 f2 : LTL_formula) :=
Not ( Or (Not f1) (Not f2)).

Definition F := Not T.

Definition Release (f1 f2: LTL_formula) :=
Not (Until (Not f1) (Not f2)).

Definition Eventually (f : LTL_formula) :=
Until T f.

Definition Globally (f : LTL_formula) :=
Release F f.

Fixpoint EQ (f1 f2 : LTL_formula) : bool :=
match f1 with
| T => match f2 with 
	| T => true  
	| P _ => false
	| Or fa fb => orb (EQ T fa)(EQ T fb)
	| Not f => EQ (Not T) f
	| Next f => EQ T f
	| Until fa fb => EQ T fb
	end
| P n => match f2 with
	| T => false
	| P n => true
	| Or fa fb => 
		orb 
		(andb (EQ T fa) (EQ (P n) fb))
		(andb (EQ T fb) (EQ (P n) fa))
	| Not f => EQ (Not (P n)) (f)
	| Next f => false
	| Until fa fb => andb (EQ (P n) fa) (EQ (P n) fb)
	| _ => false
	end
| Or fx fy => match f2 with
	| T => orb (EQ T fx) (EQ T fy)
	| P n => orb 
		(andb (EQ fx T) (EQ fx (P n)))
		(andb (EQ fy T) (EQ fy (P n)))
	| Or fa fb => orb 
		(andb (EQ fx fa) (EQ fy fb))
		(andb (EQ fy fa) (EQ fx fb))
	| Next f => match fx, fy with 
			| Next fx', Next fy' => EQ (Or fx' fy') f
			| _ , _ => false
			end
	| _ => false
	end
| _ => false
end.



Theorem T_is_T: EQ T T = true.
Proof.
reflexivity.
Qed.

Theorem F_is_not_T: semantic_equality F T = false.
Proof.
reflexivity.
Qed.

Theorem T_is_not_F: semantic_equality F T = false.
Proof.
reflexivity.
Qed.

