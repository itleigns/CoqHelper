Add LoadPath "BasicProperty" as BasicProperty.
Add LoadPath "MyAlgebraicStructure" as MyAlgebraicStructure.
Add LoadPath "Tools" as Tools.

From mathcomp Require Import ssreflect.

Require Import MyAlgebraicStructure.MyField.

Record CommutativeMonoid : Type := mkCommutativeMonoid
{
CMT : Type;
CMe : CMT;
CMc : CMT -> CMT -> CMT;
CM_comm : forall (x y : CMT), (CMc x y) = (CMc y x);
CM_O_r : forall (x : CMT), (CMc x CMe) = x;
CM_assoc : forall (x y z : CMT), (CMc (CMc x y) z) = (CMc x (CMc y z))
}.

Lemma CM_O_l : forall (CM : CommutativeMonoid) (x : CMT CM), CMc CM (CMe CM) x = x.
Proof.
intros CM x.
rewrite (CM_comm CM (CMe CM) x).
apply (CM_O_r CM x).
Qed.

Lemma CM_compat_l : forall (CM : CommutativeMonoid) (x y z: CMT CM), y = z -> CMc CM x y = CMc CM x z.
Proof.
intros CM x y z H1.
rewrite H1.
reflexivity.
Qed.

Ltac eliminate_O_CM CM expression := match expression with
  | (CMc CM (CMe CM) ?b) => rewrite (CM_O_l CM b); idtac "rewrite (CM_O_l" CM b ")."
  | (CMc CM ?a (CMe CM)) => rewrite (CM_O_r CM a); idtac "rewrite (CM_O_r" CM a ")."
  | (CMc CM ?a ?b) => eliminate_O_CM CM a
  | (CMc CM ?a ?b) => eliminate_O_CM CM b
end.

Ltac assoc_normalize_expression_CM CM expression := match expression with
  | (CMc CM ?a ?b) => match a with
    | (CMc CM ?d ?e) => rewrite (CM_assoc CM d e b); idtac "rewrite (CM_assoc" CM d e b ")."
    | _ => assoc_normalize_expression_CM CM b
  end
end.

Ltac move_to_first_CM CM var expression := match expression with
  | (CMc CM ?a var) =>
    rewrite (CM_comm CM a var);
    idtac "rewrite (CM_comm" CM a var ")."
  | (CMc CM ?a (CMc CM var ?b)) =>
    rewrite - (CM_assoc CM a var b); 
    idtac "rewrite - (CM_assoc" CM a var b ").";
    rewrite (CM_comm CM a var);
    idtac "rewrite (CM_comm" CM a var ").";
    rewrite (CM_assoc CM var a b); 
    idtac "rewrite (CM_assoc" CM var a b ")."
  | (CMc CM ?a ?b) => move_to_first_CM CM var b
end.

Ltac equal_CM CM := repeat match goal with
  | [|- ?a = ?b] => eliminate_O_CM CM a
end; repeat match goal with
  | [|- ?a = ?b] => eliminate_O_CM CM b
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_expression_CM CM a
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_expression_CM CM b
end; repeat match goal with
  | [|- CMc CM ?a ?b = CMc CM ?a ?c] => apply (CM_compat_l CM a b c); idtac "apply (CM_compat_l" CM a b c ")."
  | [|- CMc CM ?a ?b = ?c] => move_to_first_CM CM a c
  | _ => reflexivity; idtac "reflexivity."
end.

Record CommutativeGroup : Type := mkCommutativeGroup
{
CGT : Type;
CGe : CGT;
CGc : CGT -> CGT -> CGT;
CGo : CGT -> CGT;
CG_comm : forall (x y : CGT), (CGc x y) = (CGc y x);
CG_O_r : forall (x : CGT), (CGc x CGe) = x;
CG_assoc : forall (x y z : CGT), (CGc (CGc x y) z) = (CGc x (CGc y z));
CG_opp_r : forall (x : CGT), (CGc x (CGo x)) = CGe;
}.

Lemma CG_O_l : forall (CG : CommutativeGroup) (x : CGT CG), CGc CG (CGe CG) x = x.
Proof.
intros CG x.
rewrite (CG_comm CG (CGe CG) x).
apply (CG_O_r CG x).
Qed.

Lemma CG_compat_l : forall (CG : CommutativeGroup) (x y z : CGT CG), y = z -> CGc CG x y = CGc CG x z.
Proof.
intros CG x y z H1.
rewrite H1.
reflexivity.
Qed.

Lemma CG_opp_l : forall (CG : CommutativeGroup) (x : CGT CG), CGc CG (CGo CG x) x = CGe CG.
Proof.
intros CG x.
rewrite (CG_comm CG (CGo CG x) x).
apply (CG_opp_r CG x).
Qed.

Lemma CG_opp_r_uniq : forall (CG : CommutativeGroup) (x y : CGT CG), (CGc CG x y) = (CGe CG) -> y = (CGo CG x).
Proof.
move=> CG x y H1.
suff: (CGc CG (CGo CG x) (CGc CG x y)) = (CGc CG (CGo CG x) (CGe CG)).
move=> H2.
rewrite - (CG_O_r CG (CGo CG x)).
rewrite - H2.
rewrite - (CG_assoc CG (CGo CG x) x y).
rewrite (CG_opp_l CG x).
rewrite (CG_O_l CG y).
reflexivity.
rewrite H1.
reflexivity.
Qed.

Lemma CG_opp_involutive : forall (CG : CommutativeGroup) (x : CGT CG), (CGo CG (CGo CG x)) = x.
Proof.
move=> CG x.
suff: (x = CGo CG (CGo CG x)).
move=> H1.
rewrite {2} H1.
reflexivity.
apply (CG_opp_r_uniq CG (CGo CG x)).
apply (CG_opp_l CG x).
Qed.

Lemma CG_opp_O : forall (CG : CommutativeGroup), (CGo CG (CGe CG)) = (CGe CG).
Proof.
move=> CG.
rewrite {2} (CG_opp_r_uniq CG (CGe CG) (CGe CG)).
reflexivity.
apply (CG_O_l CG (CGe CG)).
Qed.

Lemma CG_opp_distr : forall (CG : CommutativeGroup) (x y : CGT CG), (CGo CG (CGc CG x y)) = (CGc CG (CGo CG x) (CGo CG y)).
Proof.
move=> CG x y.
suff: (CGc CG (CGo CG x) (CGo CG y) = CGo CG (CGc CG x y)).
move=> H1.
rewrite H1.
reflexivity.
apply (CG_opp_r_uniq CG (CGc CG x y)).
rewrite (CG_comm CG x y).
rewrite - (CG_assoc CG (CGc CG y x) (CGo CG x) (CGo CG y)).
rewrite (CG_assoc CG y x (CGo CG x)).
rewrite (CG_opp_r CG x).
rewrite (CG_O_r CG y).
apply (CG_opp_r CG y).
Qed.

Ltac eliminate_opp_opp_CG CG expression := match expression with
  | (CGo CG (CGo CG ?a)) => rewrite (CG_opp_involutive CG a); idtac "rewrite (CG_opp_involutive" CG a ")."
  | (CGc CG ?a ?b) => eliminate_opp_opp_CG CG a
  | (CGc CG ?a ?b) => eliminate_opp_opp_CG CG b
end.

Ltac eliminate_O_CG CG expression := match expression with
  | (CGc CG (CGe CG) ?b) => rewrite (CG_O_l CG b); idtac "rewrite (CG_O_l" CG b ")."
  | (CGc CG ?a (CGe CG)) => rewrite (CG_O_r CG a); idtac "rewrite (CG_O_r" CG a ")."
  | (CGc CG ?a ?b) => eliminate_O_CG CG a
  | (CGc CG ?a ?b) => eliminate_O_CG CG b
end.

Ltac eliminate_opp_distr_CG CG expression := match expression with
  | (CGo CG (CGc CG ?a ?b)) => rewrite (CG_opp_distr CG a b); idtac "rewrite (CG_opp_distr" CG a b ")."
  | (CGc CG ?a ?b) => eliminate_opp_distr_CG CG a
  | (CGc CG ?a ?b) => eliminate_opp_distr_CG CG b
end.

Ltac assoc_normalize_expression_CG CG expression := match expression with
  | (CGc CG ?a ?b) => match a with
    | (CGc CG ?d ?e) => rewrite (CG_assoc CG d e b); idtac "rewrite (CG_assoc" CG d e b ")."
    | _ => assoc_normalize_expression_CG CG b
  end
end.

Ltac move_to_first_CG CG var expression := match expression with
  | (CGc CG ?a var) =>
    rewrite (CG_comm CG a var);
    idtac "rewrite (CG_comm" CG a var ")."
  | (CGc CG ?a (CGc CG var ?b)) =>
    rewrite - (CG_assoc CG a var b); 
    idtac "rewrite - (CG_assoc" CG a var b ").";
    rewrite (CG_comm CG a var);
    idtac "rewrite (CG_comm" CG a var ").";
    rewrite (CG_assoc CG var a); 
    idtac "rewrite (CG_assoc" CG var a ")."
  | (CGc CG ?a ?b) => move_to_first_CG CG var b
end.

Ltac include_term_CG CG var expression arg := match expression with
  | var => move_to_first_CG CG var arg
  | (CGc CG ?a var) => move_to_first_CG CG var arg
  | (CGc CG var ?b) => move_to_first_CG CG var arg
  | (CGc CG ?a ?b) => include_term_CG CG var a arg
  | (CGc CG ?a ?b) => include_term_CG CG var b arg
end.

Ltac eliminate_opp_CG CG expression := match expression with
  | (CGc CG (CGo CG ?a) ?a) => rewrite (CG_opp_l CG a); idtac "rewrite (CG_opp_l" CG a ")."
  | (CGc CG ?a (CGo CG ?a)) => rewrite (CG_opp_r CG a); idtac "rewrite (CG_opp_r" CG a ")."
  | (CGc CG (CGo CG ?a) (CGc CG ?a ?b)) => rewrite - (CG_assoc CG (CGo CG a) a b); idtac "rewrite - (CG_assoc" CG "(CGo" CG a ")" a b ").";
    rewrite (CG_opp_l CG a); idtac "rewrite (CG_opp_l" CG a ").";
    rewrite (CG_O_l CG b); idtac "rewrite (CG_O_l" CG b ")."
  | (CGc CG ?a (CGc CG (CGo CG ?a) ?b)) => rewrite - (CG_assoc CG a (CGo CG a) b); idtac "rewrite - (CG_assoc" CG a "(CGo" CG a ")" b ").";
    rewrite (CG_opp_r CG a); idtac "rewrite (CG_opp_r" CG a ").";
    rewrite (CG_O_l CG b); idtac "rewrite (CG_O_l" CG b ")."
  | (CGc CG (CGo CG ?a) ?b) => include_term_CG CG a b b
  | (CGc CG ?a ?b) => include_term_CG CG (CGo CG a) b b
end.

Ltac equal_CG CG := repeat match goal with
  | [|- ?a = ?b] => eliminate_opp_opp_CG CG a
  | [|- ?a = ?b] => eliminate_opp_opp_CG CG b
  | [|- ?a = ?b] => eliminate_O_CG CG a
  | [|- ?a = ?b] => eliminate_O_CG CG b
  | [|- ?a = ?b] => eliminate_opp_distr_CG CG a
  | [|- ?a = ?b] => eliminate_opp_distr_CG CG b
  | _ => rewrite CG_opp_O; idtac "rewrite CG_opp_O."
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_expression_CG CG a
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_expression_CG CG b
end; repeat match goal with
  | [|- CGc CG ?a ?b = CGc CG ?a ?c] => apply (CG_compat_l CG a b c); idtac "apply (CG_compat_l" CG a b c ")."
  | [|- ?a = ?b] => eliminate_opp_CG CG a
  | [|- ?a = ?b] => eliminate_opp_CG CG b
  | [|- CGc CG ?a ?b = ?c] => move_to_first_CG CG a c
  | _ => reflexivity; idtac "reflexivity."
end.

Record Ring : Type := mkRing
{
RiT   : Type;
RiO : RiT;
RiI : RiT;
Riadd : RiT -> RiT -> RiT;
Rimul : RiT -> RiT -> RiT;
Riopp : RiT -> RiT;
Riadd_assoc : forall (x y z : RiT), (Riadd (Riadd x y) z) = (Riadd x (Riadd y z));
Rimul_assoc : forall (x y z : RiT), (Rimul (Rimul x y) z) = (Rimul x (Rimul y z));
Riadd_comm : forall (x y : RiT), (Riadd x y) = (Riadd y x);
Riadd_O_l : forall x : RiT, (Riadd RiO x) = x;
Rimul_I_l : forall x : RiT, (Rimul RiI x) = x;
Rimul_I_r : forall x : RiT, (Rimul x RiI) = x;
Riadd_opp_r : forall x : RiT, (Riadd x (Riopp x)) = RiO;
Rimul_add_distr_l : forall (x y z : RiT), (Rimul x (Riadd y z)) = (Riadd (Rimul x y) (Rimul x z));
Rimul_add_distr_r : forall (x y z : RiT), (Rimul (Riadd x y) z) = (Riadd (Rimul x z) (Rimul y z));
RiI_neq_RiO : RiI <> RiO
}.

Lemma Riadd_O_r : forall (ri : Ring) (x : RiT ri), (Riadd ri x (RiO ri)) = x.
Proof.
move=> ri x.
rewrite (Riadd_comm ri x (RiO ri)).
apply (Riadd_O_l ri x).
Qed.

Lemma Riadd_eq_compat_l : forall (ri : Ring) (x y z : RiT ri), y = z -> (Riadd ri x y) = (Riadd ri x z).
Proof.
move=> ri x y z H1.
rewrite H1.
reflexivity.
Qed.

Lemma Riadd_opp_l : forall (ri : Ring) (x : RiT ri), (Riadd ri (Riopp ri x) x) = (RiO ri).
Proof.
move=> ri x.
rewrite (Riadd_comm ri (Riopp ri x) x).
apply (Riadd_opp_r ri x).
Qed.

Lemma Riadd_O_r_uniq : forall (ri : Ring) (x y : RiT ri), (Riadd ri x y) = x -> y = (RiO ri).
Proof.
move=> ri x y H1.
rewrite - (Riadd_O_l ri y).
rewrite - (Riadd_opp_l ri x).
rewrite (Riadd_assoc ri (Riopp ri x) x y).
rewrite H1.
reflexivity.
Qed.

Lemma Rimul_O_r : forall (ri : Ring) (x : RiT ri), (Rimul ri x (RiO ri)) = (RiO ri).
Proof.
move=> ri x.
apply (Riadd_O_r_uniq ri (Rimul ri x (RiO ri)) (Rimul ri x (RiO ri))).
rewrite - (Rimul_add_distr_l ri x (RiO ri) (RiO ri)).
rewrite (Riadd_O_l ri (RiO ri)).
reflexivity.
Qed.

Lemma Rimul_O_l : forall (ri : Ring) (x : RiT ri), (Rimul ri (RiO ri) x) = (RiO ri).
Proof.
move=> ri x.
apply (Riadd_O_r_uniq ri (Rimul ri (RiO ri) x) (Rimul ri (RiO ri) x)).
rewrite - (Rimul_add_distr_r ri (RiO ri) (RiO ri) x).
rewrite (Riadd_O_l ri (RiO ri)).
reflexivity.
Qed.

Lemma Riadd_opp_r_uniq : forall (ri : Ring) (x y : RiT ri), (Riadd ri x y) = (RiO ri) -> y = (Riopp ri x).
Proof.
move=> ri x y H1.
suff: (Riadd ri (Riopp ri x) (Riadd ri x y)) = (Riadd ri (Riopp ri x) (RiO ri)).
move=> H2.
rewrite - (Riadd_O_r ri (Riopp ri x)).
rewrite - H2.
rewrite - (Riadd_assoc ri (Riopp ri x) x y).
rewrite (Riadd_opp_l ri x).
rewrite (Riadd_O_l ri y).
reflexivity.
rewrite H1.
reflexivity.
Qed.

Lemma Riopp_involutive : forall (ri : Ring) (x : RiT ri), (Riopp ri (Riopp ri x)) = x.
Proof.
move=> ri x.
suff: (x = Riopp ri (Riopp ri x)).
move=> H1.
rewrite {2} H1.
reflexivity.
apply (Riadd_opp_r_uniq ri (Riopp ri x)).
apply (Riadd_opp_l ri x).
Qed.

Lemma Riopp_O : forall (ri : Ring), (Riopp ri (RiO ri)) = (RiO ri).
Proof.
move=> ri.
rewrite {2} (Riadd_opp_r_uniq ri (RiO ri) (RiO ri)).
reflexivity.
apply (Riadd_O_l ri (RiO ri)).
Qed.

Lemma Riopp_add_distr : forall (ri : Ring) (x y : RiT ri), (Riopp ri (Riadd ri x y)) = (Riadd ri (Riopp ri x) (Riopp ri y)).
Proof.
move=> ri x y.
suff: (Riadd ri (Riopp ri x) (Riopp ri y) = Riopp ri (Riadd ri x y)).
move=> H1.
rewrite H1.
reflexivity.
apply (Riadd_opp_r_uniq ri (Riadd ri x y)).
rewrite (Riadd_comm ri x y).
rewrite - (Riadd_assoc ri (Riadd ri y x) (Riopp ri x) (Riopp ri y)).
rewrite (Riadd_assoc ri y x (Riopp ri x)).
rewrite (Riadd_opp_r ri x).
rewrite (Riadd_O_r ri y).
apply (Riadd_opp_r ri y).
Qed.

Lemma Riopp_mul_distr_l_reverse : forall (ri : Ring) (x y : RiT ri), Rimul ri (Riopp ri x) y = Riopp ri (Rimul ri x y).
Proof.
move=> ri x y.
apply (Riadd_opp_r_uniq ri (Rimul ri x y)).
rewrite - (Rimul_add_distr_r ri x (Riopp ri x) y).
rewrite (Riadd_opp_r ri x).
apply (Rimul_O_l ri y).
Qed.

Lemma Riopp_mul_distr_r_reverse : forall (ri : Ring) (x y : RiT ri), Rimul ri x (Riopp ri y) = Riopp ri (Rimul ri x y).
Proof.
move=> ri x y.
apply (Riadd_opp_r_uniq ri (Rimul ri x y)).
rewrite - (Rimul_add_distr_l ri x y (Riopp ri y)).
rewrite (Riadd_opp_r ri y).
apply (Rimul_O_r ri x).
Qed.

Lemma Rimul_opp_opp : forall (ri : Ring) (x y : RiT ri), Rimul ri (Riopp ri x) (Riopp ri y) = Rimul ri x y.
Proof.
move=> ri x y.
rewrite (Riopp_mul_distr_l_reverse ri x (Riopp ri y)).
rewrite (Riopp_mul_distr_r_reverse ri x y).
apply (Riopp_involutive ri (Rimul ri x y)).
Qed.

Ltac eliminate_distr_Ri ri expression := match expression with
  | (Riopp ri (Riopp ri ?a)) => rewrite (Riopp_involutive ri a); idtac "rewrite (Riopp_involutive" ri a ")."
  | (Riopp ri (RiO ri)) => rewrite (Riopp_O ri); idtac "rewrite (Riopp_O" ri ")."
  | (Rimul ri (RiO ri) ?a) => rewrite (Rimul_O_l ri a); idtac "rewrite (Rimul_O_l" ri a ")."
  | (Rimul ri ?a (RiO ri)) => rewrite (Rimul_O_r ri a); idtac "rewrite (Rimul_O_r" ri a ")."
  | (Rimul ri (RiI ri) ?a) => rewrite (Rimul_I_l ri a); idtac "rewrite (Rimul_I_l" ri a ")."
  | (Rimul ri ?a (RiI ri)) => rewrite (Rimul_I_r ri a); idtac "rewrite (Rimul_I_r" ri a ")."
  | (Riadd ri (RiO ri) ?a) => rewrite (Riadd_O_l ri a); idtac "rewrite (Riadd_O_l" ri a ")."
  | (Riadd ri ?a (RiO ri)) => rewrite (Riadd_O_r ri a); idtac "rewrite (Riadd_O_r" ri a ")."
  | (Riopp ri (Riadd ri ?a ?b)) => rewrite (Riopp_add_distr ri a b); idtac "rewrite (Riopp_add_distr" ri a b ")."
  | (Rimul ri ?a (Riadd ri ?b ?c)) => rewrite (Rimul_add_distr_l ri a b c); idtac "rewrite (Rimul_add_distr_l" ri a b c ")."
  | (Rimul ri (Riadd ri ?a ?b) ?c) => rewrite (Rimul_add_distr_r ri a b c); idtac "rewrite (Rimul_add_distr_r" ri a b c ")."
  | (Riopp ri ?a) => eliminate_distr_Ri ri a
  | (Riadd ri ?a ?b) => eliminate_distr_Ri ri a
  | (Riadd ri ?a ?b) => eliminate_distr_Ri ri b
  | (Rimul ri ?a ?b) => eliminate_distr_Ri ri a
  | (Rimul ri ?a ?b) => eliminate_distr_Ri ri b
end.

Ltac assoc_normalize_add_expression_Ri ri expression := match expression with
  | (Riadd ri ?a ?b) => match a with
    | (Riadd ri ?d ?e) => rewrite (Riadd_assoc ri d e b); idtac "rewrite (Riadd_assoc" ri d e b ")."
    | _ => assoc_normalize_add_expression_Ri ri b
  end
end.

Ltac put_out_opp_each_monomial_Ri ri expression := match expression with
  | (Riadd ri ?a ?b) => put_out_opp_each_monomial_Ri ri a
  | (Riadd ri ?a ?b) => put_out_opp_each_monomial_Ri ri b
  | (Riopp ri (Riopp ri ?a)) => rewrite (Riopp_involutive ri a); idtac "rewrite (Riopp_involutive" ri a ")."
  | (Riopp ri ?a) => put_out_opp_each_monomial_Ri ri a
  | (Rimul ri (RiI ri) ?a) => rewrite (Rimul_I_l ri a); idtac "rewrite (Rimul_I_l" ri a ")."
  | (Rimul ri ?a (RiI ri)) => rewrite (Rimul_I_r ri a); idtac "rewrite (Rimul_I_r" ri a ")."
  | (Rimul ri ?a ?b) => put_out_opp_each_monomial_Ri ri a
  | (Rimul ri ?a ?b) => put_out_opp_each_monomial_Ri ri b
  | (Rimul ri (Riopp ri ?a) (Riopp ri ?b)) => rewrite (Rimul_opp_opp ri a b); idtac "rewrite (Rimul_opp_opp" ri a b ")."
  | (Rimul ri ?a (Riopp ri ?b)) => rewrite (Riopp_mul_distr_r_reverse ri a b); idtac "rewrite (Riopp_mul_distr_r_reverse" ri a b ")."
  | (Rimul ri (Riopp ri ?a) ?b) => rewrite (Riopp_mul_distr_l_reverse ri a b); idtac "rewrite (Riopp_mul_distr_l_reverse" ri a b ")."
end.

Ltac assoc_normalize_mul_expression_Ri ri expression := match expression with
  | (Rimul ri ?a ?b) => match a with
    | (Rimul ri ?d ?e) => rewrite (Rimul_assoc ri d e b); idtac "rewrite (Rimul_assoc" ri d e b ")."
    | _ => assoc_normalize_mul_expression_Ri ri b
  end
  | (Riopp ri ?a) => assoc_normalize_mul_expression_Ri ri a
  | (Riadd ri ?a ?b) => assoc_normalize_mul_expression_Ri ri a
  | (Riadd ri ?a ?b) => assoc_normalize_mul_expression_Ri ri b
end.

Ltac move_to_first_Ri ri var expression := match expression with
  | (Riadd ri ?a var) =>
    rewrite (Riadd_comm ri a var);
    idtac "rewrite (Riadd_comm" ri a var ")."
  | (Riadd ri ?a (Riadd ri var ?b)) =>
    rewrite - (Riadd_assoc ri a var b); 
    idtac "rewrite - (Riadd_assoc" ri a var b ").";
    rewrite (Riadd_comm ri a var);
    idtac "rewrite (Riadd_comm" ri a var ").";
    rewrite (Riadd_assoc ri var a); 
    idtac "rewrite (Riadd_assoc" ri var a ")."
  | (Riadd ri ?a ?b) => move_to_first_Ri ri var b
end.

Ltac include_term_Ri ri var expression arg := match expression with
  | var => move_to_first_Ri ri var arg
  | (Riadd ri ?a var) => move_to_first_Ri ri var arg
  | (Riadd ri var ?b) => move_to_first_Ri ri var arg
  | (Riadd ri ?a ?b) => include_term_Ri ri var b arg
end.

Ltac eliminate_opp_Ri ri expression := match expression with
  | (Riadd ri (Riopp ri ?a) ?a) => rewrite (Riadd_opp_l ri a); idtac "rewrite (Riadd_opp_l" ri a ")."
  | (Riadd ri ?a (Riopp ri ?a)) => rewrite (Riadd_opp_r ri a); idtac "rewrite (Riadd_opp_r" ri a ")."
  | (Riadd ri (Riopp ri ?a) (Riadd ri ?a ?b)) => rewrite - (Riadd_assoc ri (Riopp ri a) a b); idtac "rewrite - (Riadd_assoc" ri "(Riopp" ri a ")" a b ").";
    rewrite (Riadd_opp_l ri a); idtac "rewrite (Riadd_opp_l" ri a ").";
    rewrite (Riadd_O_l ri b); idtac "rewrite (Riadd_O_l" ri b ")."
  | (Riadd ri ?a (Riadd ri (Riopp ri ?a) ?b)) => rewrite - (Riadd_assoc ri a (Riopp ri a) b); idtac "rewrite - (Riadd_assoc" ri a "(Riopp" ri a ")" b ").";
    rewrite (Riadd_opp_r ri a); idtac "rewrite (Riadd_opp_r" ri a ").";
    rewrite (Riadd_O_l ri b); idtac "rewrite (Riadd_O_l" ri b ")."
  | (Riadd ri (Riopp ri ?a) ?b) => include_term_Ri ri a b b
  | (Riadd ri ?a ?b) => include_term_Ri ri (Riopp ri a) b b
end.

Ltac equal_Ri ri := repeat match goal with
  | [|- ?a = ?b] => eliminate_distr_Ri ri a
end; repeat match goal with
  | [|- ?a = ?b] => eliminate_distr_Ri ri b
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_add_expression_Ri ri a
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_add_expression_Ri ri b
end; repeat match goal with
  | [|- ?a = ?b] => put_out_opp_each_monomial_Ri ri a
end; repeat match goal with
  | [|- ?a = ?b] => put_out_opp_each_monomial_Ri ri b
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_mul_expression_Ri ri a
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_mul_expression_Ri ri b
end; repeat match goal with
  | [|- Riadd ri ?a ?b = Riadd ri ?a ?c] => apply (Riadd_eq_compat_l ri a b c); idtac "apply (Riadd_eq_compat_l" ri a b c ")."
  | [|- ?a = ?b] => eliminate_opp_Ri ri a
  | [|- ?a = ?b] => eliminate_opp_Ri ri b
  | [|- Riadd ri ?a ?b = ?c] => move_to_first_Ri ri a c
  | _ => reflexivity; idtac "reflexivity."
end.

Record CommutativeRing : Type := mkCommutativeRing
{
CRiT   : Type;
CRiO : CRiT;
CRiI : CRiT;
CRiadd : CRiT -> CRiT -> CRiT;
CRimul : CRiT -> CRiT -> CRiT;
CRiopp : CRiT -> CRiT;
CRiadd_assoc : forall (x y z : CRiT), (CRiadd (CRiadd x y) z) = (CRiadd x (CRiadd y z));
CRimul_assoc : forall (x y z : CRiT), (CRimul (CRimul x y) z) = (CRimul x (CRimul y z));
CRiadd_comm : forall (x y : CRiT), (CRiadd x y) = (CRiadd y x);
CRimul_comm : forall (x y : CRiT), (CRimul x y) = (CRimul y x);
CRiadd_O_l : forall x : CRiT, (CRiadd CRiO x) = x;
CRimul_I_l : forall x : CRiT, (CRimul CRiI x) = x;
CRimul_I_r : forall x : CRiT, (CRimul x CRiI) = x;
CRiadd_opp_r : forall x : CRiT, (CRiadd x (CRiopp x)) = CRiO;
CRimul_add_distr_l : forall (x y z : CRiT), (CRimul x (CRiadd y z)) = (CRiadd (CRimul x y) (CRimul x z));
CRimul_add_distr_r : forall (x y z : CRiT), (CRimul (CRiadd x y) z) = (CRiadd (CRimul x z) (CRimul y z));
CRiI_neq_CRiO : CRiI <> CRiO
}.

Lemma CRiadd_O_r : forall (cri : CommutativeRing) (x : CRiT cri), (CRiadd cri x (CRiO cri)) = x.
Proof.
move=> cri x.
rewrite (CRiadd_comm cri x (CRiO cri)).
apply (CRiadd_O_l cri x).
Qed.

Lemma CRiadd_eq_compat_l : forall (cri : CommutativeRing) (x y z : CRiT cri), y = z -> (CRiadd cri x y) = (CRiadd cri x z).
Proof.
move=> cri x y z H1.
rewrite H1.
reflexivity.
Qed.

Lemma CRiadd_opp_l : forall (cri : CommutativeRing) (x : CRiT cri), (CRiadd cri (CRiopp cri x) x) = (CRiO cri).
Proof.
move=> cri x.
rewrite (CRiadd_comm cri (CRiopp cri x) x).
apply (CRiadd_opp_r cri x).
Qed.

Lemma CRiadd_O_r_uniq : forall (cri : CommutativeRing) (x y : CRiT cri), (CRiadd cri x y) = x -> y = (CRiO cri).
Proof.
move=> cri x y H1.
rewrite - (CRiadd_O_l cri y).
rewrite - (CRiadd_opp_l cri x).
rewrite (CRiadd_assoc cri (CRiopp cri x) x y).
rewrite H1.
reflexivity.
Qed.

Lemma CRimul_O_r : forall (cri : CommutativeRing) (x : CRiT cri), (CRimul cri x (CRiO cri)) = (CRiO cri).
Proof.
move=> cri x.
apply (CRiadd_O_r_uniq cri (CRimul cri x (CRiO cri)) (CRimul cri x (CRiO cri))).
rewrite - (CRimul_add_distr_l cri x (CRiO cri) (CRiO cri)).
rewrite (CRiadd_O_l cri (CRiO cri)).
reflexivity.
Qed.

Lemma CRimul_O_l : forall (cri : CommutativeRing) (x : CRiT cri), (CRimul cri (CRiO cri) x) = (CRiO cri).
Proof.
move=> cri x.
apply (CRiadd_O_r_uniq cri (CRimul cri (CRiO cri) x) (CRimul cri (CRiO cri) x)).
rewrite - (CRimul_add_distr_r cri (CRiO cri) (CRiO cri) x).
rewrite (CRiadd_O_l cri (CRiO cri)).
reflexivity.
Qed.

Lemma CRiadd_opp_r_uniq : forall (cri : CommutativeRing) (x y : CRiT cri), (CRiadd cri x y) = (CRiO cri) -> y = (CRiopp cri x).
Proof.
move=> cri x y H1.
suff: (CRiadd cri (CRiopp cri x) (CRiadd cri x y)) = (CRiadd cri (CRiopp cri x) (CRiO cri)).
move=> H2.
rewrite - (CRiadd_O_r cri (CRiopp cri x)).
rewrite - H2.
rewrite - (CRiadd_assoc cri (CRiopp cri x) x y).
rewrite (CRiadd_opp_l cri x).
rewrite (CRiadd_O_l cri y).
reflexivity.
rewrite H1.
reflexivity.
Qed.

Lemma CRiopp_involutive : forall (cri : CommutativeRing) (x : CRiT cri), (CRiopp cri (CRiopp cri x)) = x.
Proof.
move=> cri x.
suff: (x = CRiopp cri (CRiopp cri x)).
move=> H1.
rewrite {2} H1.
reflexivity.
apply (CRiadd_opp_r_uniq cri (CRiopp cri x)).
apply (CRiadd_opp_l cri x).
Qed.

Lemma CRiopp_O : forall (cri : CommutativeRing), (CRiopp cri (CRiO cri)) = (CRiO cri).
Proof.
move=> cri.
rewrite {2} (CRiadd_opp_r_uniq cri (CRiO cri) (CRiO cri)).
reflexivity.
apply (CRiadd_O_l cri (CRiO cri)).
Qed.

Lemma CRiopp_add_distr : forall (cri : CommutativeRing) (x y : CRiT cri), (CRiopp cri (CRiadd cri x y)) = (CRiadd cri (CRiopp cri x) (CRiopp cri y)).
Proof.
move=> cri x y.
suff: (CRiadd cri (CRiopp cri x) (CRiopp cri y) = CRiopp cri (CRiadd cri x y)).
move=> H1.
rewrite H1.
reflexivity.
apply (CRiadd_opp_r_uniq cri (CRiadd cri x y)).
rewrite (CRiadd_comm cri x y).
rewrite - (CRiadd_assoc cri (CRiadd cri y x) (CRiopp cri x) (CRiopp cri y)).
rewrite (CRiadd_assoc cri y x (CRiopp cri x)).
rewrite (CRiadd_opp_r cri x).
rewrite (CRiadd_O_r cri y).
apply (CRiadd_opp_r cri y).
Qed.

Lemma CRiopp_mul_distr_l_reverse : forall (cri : CommutativeRing) (x y : CRiT cri), CRimul cri (CRiopp cri x) y = CRiopp cri (CRimul cri x y).
Proof.
move=> cri x y.
apply (CRiadd_opp_r_uniq cri (CRimul cri x y)).
rewrite - (CRimul_add_distr_r cri x (CRiopp cri x) y).
rewrite (CRiadd_opp_r cri x).
apply (CRimul_O_l cri y).
Qed.

Lemma CRiopp_mul_distr_r_reverse : forall (cri : CommutativeRing) (x y : CRiT cri), CRimul cri x (CRiopp cri y) = CRiopp cri (CRimul cri x y).
Proof.
move=> cri x y.
apply (CRiadd_opp_r_uniq cri (CRimul cri x y)).
rewrite - (CRimul_add_distr_l cri x y (CRiopp cri y)).
rewrite (CRiadd_opp_r cri y).
apply (CRimul_O_r cri x).
Qed.

Lemma CRimul_opp_opp : forall (cri : CommutativeRing) (x y : CRiT cri), CRimul cri (CRiopp cri x) (CRiopp cri y) = CRimul cri x y.
Proof.
move=> cri x y.
rewrite (CRiopp_mul_distr_l_reverse cri x (CRiopp cri y)).
rewrite (CRiopp_mul_distr_r_reverse cri x y).
apply (CRiopp_involutive cri (CRimul cri x y)).
Qed.

Ltac eliminate_distr_CRi cri expression := match expression with
  | (CRiopp cri (CRiopp cri ?a)) => rewrite (CRiopp_involutive cri a); idtac "rewrite (CRiopp_involutive" cri a ")."
  | (CRiopp cri (CRiO cri)) => rewrite (CRiopp_O cri); idtac "rewrite (CRiopp_O" cri ")."
  | (CRimul cri (CRiO cri) ?a) => rewrite (CRimul_O_l cri a); idtac "rewrite (CRimul_O_l" cri a ")."
  | (CRimul cri ?a (CRiO cri)) => rewrite (CRimul_O_r cri a); idtac "rewrite (CRimul_O_r" cri a ")."
  | (CRimul cri (CRiI cri) ?a) => rewrite (CRimul_I_l cri a); idtac "rewrite (CRimul_I_l" cri a ")."
  | (CRimul cri ?a (CRiI cri)) => rewrite (CRimul_I_r cri a); idtac "rewrite (CRimul_I_r" cri a ")."
  | (CRiadd cri (CRiO cri) ?a) => rewrite (CRiadd_O_l cri a); idtac "rewrite (CRiadd_O_l" cri a ")."
  | (CRiadd cri ?a (CRiO cri)) => rewrite (CRiadd_O_r cri a); idtac "rewrite (CRiadd_O_r" cri a ")."
  | (CRiopp cri (CRiadd cri ?a ?b)) => rewrite (CRiopp_add_distr cri a b); idtac "rewrite (CRiopp_add_distr" cri a b ")."
  | (CRimul cri ?a (CRiadd cri ?b ?c)) => rewrite (CRimul_add_distr_l cri a b c); idtac "rewrite (CRimul_add_distr_l" cri a b c ")."
  | (CRimul cri (CRiadd cri ?a ?b) ?c) => rewrite (CRimul_add_distr_r cri a b c); idtac "rewrite (CRimul_add_distr_r" cri a b c ")."
  | (CRiopp cri ?a) => eliminate_distr_CRi cri a
  | (CRiadd cri ?a ?b) => eliminate_distr_CRi cri a
  | (CRiadd cri ?a ?b) => eliminate_distr_CRi cri b
  | (CRimul cri ?a ?b) => eliminate_distr_CRi cri a
  | (CRimul cri ?a ?b) => eliminate_distr_CRi cri b
end.

Ltac assoc_normalize_add_expression_CRi cri expression := match expression with
  | (CRiadd cri ?a ?b) => match a with
    | (CRiadd cri ?d ?e) => rewrite (CRiadd_assoc cri d e b); idtac "rewrite (CRiadd_assoc" cri d e b ")."
    | _ => assoc_normalize_add_expression_CRi cri b
  end
end.

Ltac put_out_opp_each_monomial_CRi cri expression := match expression with
  | (CRiadd cri ?a ?b) => put_out_opp_each_monomial_CRi cri a
  | (CRiadd cri ?a ?b) => put_out_opp_each_monomial_CRi cri b
  | (CRiopp cri (CRiopp cri ?a)) => rewrite (CRiopp_involutive cri a); idtac "rewrite (CRiopp_involutive" cri a ")."
  | (CRiopp cri ?a) => put_out_opp_each_monomial_CRi cri a
  | (CRimul cri (CRiI cri) ?a) => rewrite (CRimul_I_l cri a); idtac "rewrite (CRimul_I_l" cri a ")."
  | (CRimul cri ?a (CRiI cri)) => rewrite (CRimul_I_r cri a); idtac "rewrite (CRimul_I_r" cri a ")."
  | (CRimul cri ?a ?b) => put_out_opp_each_monomial_CRi cri a
  | (CRimul cri ?a ?b) => put_out_opp_each_monomial_CRi cri b
  | (CRimul cri (CRiopp cri ?a) (CRiopp cri ?b)) => rewrite (CRimul_opp_opp cri a b); idtac "rewrite (CRimul_opp_opp" cri a b ")."
  | (CRimul cri ?a (CRiopp cri ?b)) => rewrite (CRiopp_mul_distr_r_reverse cri a b); idtac "rewrite (CRiopp_mul_distr_r_reverse" cri a b ")."
  | (CRimul cri (CRiopp cri ?a) ?b) => rewrite (CRiopp_mul_distr_l_reverse cri a b); idtac "rewrite (CRiopp_mul_distr_l_reverse" cri a b ")."
end.

Ltac assoc_normalize_mul_expression_CRi cri expression := match expression with
  | (CRimul cri ?a ?b) => match a with
    | (CRimul cri ?d ?e) => rewrite (CRimul_assoc cri d e b); idtac "rewrite (CRimul_assoc" cri d e b ")."
    | _ => assoc_normalize_mul_expression_CRi cri b
  end
  | (CRiopp cri ?a) => assoc_normalize_mul_expression_CRi cri a
  | (CRiadd cri ?a ?b) => assoc_normalize_mul_expression_CRi cri a
  | (CRiadd cri ?a ?b) => assoc_normalize_mul_expression_CRi cri b
end.

Ltac move_to_first_mul_CRi cri var expression := match expression with
  | (CRimul cri ?a var) =>
    rewrite (CRimul_comm cri a var);
    idtac "rewrite (CRimul_comm" cri a var ")."
  | (CRimul cri ?a (CRimul cri var ?b)) =>
    rewrite - (CRimul_assoc cri a var b); 
    idtac "rewrite - (CRimul_assoc" cri a var b ").";
    rewrite (CRimul_comm cri a var);
    idtac "rewrite (CRimul_comm" cri a var ").";
    rewrite (CRimul_assoc cri var a); 
    idtac "rewrite (CRimul_assoc" cri var a ")."
  | (CRimul cri ?a ?b) => move_to_first_mul_CRi cri var b
end.

Ltac equalize_mul_CRi cri a b := match a with
  | (CRiopp cri ?a1) => match b with
    | (CRiopp cri ?b1) => equalize_mul_CRi cri a1 b1
  end
  | (CRimul cri ?a1 ?a2) => match b with
    | (CRimul cri a1 ?b2) => equalize_mul_CRi cri a2 b2
    | _ => move_to_first_mul_CRi cri a1 b
  end
end.

Ltac compare_term_sub_CRi cri a b1 b2 arg2 arg3 := match a with
  | _ => match b1 with 
    | a => match b2 with
      | (CRiI cri) => equalize_mul_CRi cri arg2 arg3
    end
  end
  | (CRimul cri ?a1 ?a2) => match b1 with
    | a1 => compare_term_sub_CRi cri a2 b2 (CRiI cri) arg2 arg3
    | (CRimul cri ?b11 ?b12) => lazymatch b11 with
      | a1 => lazymatch b2 with 
         | (CRiI cri) => compare_term_sub_CRi cri a2 b12 (CRiI cri) arg2 arg3
         | (CRiI cri) => fail
         | _ => compare_term_sub_CRi cri a2 (CRimul cri b12 b2) (CRiI cri) arg2 arg3
      end
      | (CRimul cri ?b111 ?b112) => compare_term_sub_CRi cri a (CRimul cri b111 (CRimul cri b112 b12)) b2 arg2 arg3
      | (CRimul cri ?b111 ?b112) => fail
      | _ => lazymatch b2 with 
         | (CRiI cri) => compare_term_sub_CRi cri a b12 b11 arg2 arg3
         | (CRiI cri) => fail
         | _ => compare_term_sub_CRi cri a b12 (CRimul cri b11 b2) arg2 arg3
      end
    end
  end
end.

Ltac compare_term_CRi cri a b arg2 arg3 := match a with
  | (CRiopp cri ?a1) => match b with
    | (CRiopp cri ?b1) => compare_term_CRi cri a1 b1 arg2 arg3
  end
  | _ => compare_term_sub_CRi cri a b (CRiI cri) arg2 arg3
end.

Ltac move_to_first_add_CRi cri var expression := match expression with
  | (CRiadd cri ?a var) =>
    rewrite (CRiadd_comm cri a var);
    idtac "rewrite (CRiadd_comm" cri a var ")."
  | (CRiadd cri ?a (CRiadd cri var ?b)) =>
    rewrite - (CRiadd_assoc cri a var b); 
    idtac "rewrite - (CRiadd_assoc" cri a var b ").";
    rewrite (CRiadd_comm cri a var);
    idtac "rewrite (CRiadd_comm" cri a var ").";
    rewrite (CRiadd_assoc cri var a); 
    idtac "rewrite (CRiadd_assoc" cri var a ")."
  | (CRiadd cri ?a ?b) => move_to_first_add_CRi cri var b
end.

Ltac include_same_term_CRi cri var expression := match expression with
  | (CRiadd cri ?a ?b) => compare_term_CRi cri var a var a
  | (CRiadd cri ?a ?b) => include_same_term_CRi cri var b
  | _ => lazymatch expression with
    | (CRiadd cri ?a ?b) => fail
    | _ => compare_term_CRi cri var expression var expression
  end
end.

Ltac include_term_CRi cri var expression arg := match expression with
  | var => move_to_first_add_CRi cri var arg
  | (CRiadd cri var ?b) => move_to_first_add_CRi cri var arg
  | (CRiadd cri ?a ?b) => include_term_CRi cri var b arg
end.

Ltac eliminate_opp_CRi cri expression := match expression with
  | (CRiadd cri (CRiopp cri ?a) ?a) => rewrite (CRiadd_opp_l cri a); idtac "rewrite (CRiadd_opp_l" cri a ")."
  | (CRiadd cri ?a (CRiopp cri ?a)) => rewrite (CRiadd_opp_r cri a); idtac "rewrite (CRiadd_opp_r" cri a ")."
  | (CRiadd cri (CRiopp cri ?a) (CRiadd cri ?a ?b)) => rewrite - (CRiadd_assoc cri (CRiopp cri a) a b); idtac "rewrite - (CRiadd_assoc" cri "(CRiopp" cri a ")" a b ").";
    rewrite (CRiadd_opp_l cri a); idtac "rewrite (CRiadd_opp_l" cri a ").";
    rewrite (CRiadd_O_l cri b); idtac "rewrite (CRiadd_O_l" cri b ")."
  | (CRiadd cri ?a (CRiadd cri (CRiopp cri ?a) ?b)) => rewrite - (CRiadd_assoc cri a (CRiopp cri a) b); idtac "rewrite - (CRiadd_assoc" cri a "(CRiopp" cri a ")" b ").";
    rewrite (CRiadd_opp_r cri a); idtac "rewrite (CRiadd_opp_r" cri a ").";
    rewrite (CRiadd_O_l cri b); idtac "rewrite (CRiadd_O_l" cri b ")."
  | (CRiadd cri (CRiopp cri ?a) ?b) => include_term_CRi cri a b b
  | (CRiadd cri (CRiopp cri ?a) ?b) => include_same_term_CRi cri a b
  | (CRiadd cri ?a ?b) => include_term_CRi cri (CRiopp cri a) b b
  | (CRiadd cri ?a ?b) => include_same_term_CRi cri (CRiopp cri a) b
end.

Ltac equal_CRi cri := repeat match goal with
  | [|- ?a = ?b] => eliminate_distr_CRi cri a
end; repeat match goal with
  | [|- ?a = ?b] => eliminate_distr_CRi cri b
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_add_expression_CRi cri a
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_add_expression_CRi cri b
end; repeat match goal with
  | [|- ?a = ?b] => put_out_opp_each_monomial_CRi cri a
end; repeat match goal with
  | [|- ?a = ?b] => put_out_opp_each_monomial_CRi cri b
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_mul_expression_CRi cri a
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_mul_expression_CRi cri b
end; repeat match goal with
  | _ => reflexivity; idtac "reflexivity."
  | [|- CRiadd cri ?a ?b = CRiadd cri ?a ?c] => apply (CRiadd_eq_compat_l cri a b c); idtac "apply (CRiadd_eq_compat_l" cri a b c ")."
  | [|- ?a = ?b] => eliminate_opp_CRi cri a
  | [|- ?a = ?b] => eliminate_opp_CRi cri b
  | [|- CRiadd cri ?a ?b = ?c] => include_term_CRi cri a c c
  | [|- CRiadd cri ?a ?b = ?c] => include_same_term_CRi cri a c
  | [|- CRiopp cri ?a = CRiopp cri ?b] => equalize_mul_CRi cri a b
  | [|- ?a = ?b] => equalize_mul_CRi cri a b
end.

Ltac eliminate_distr_F f expression := match expression with
  | (Fopp f (Fopp f ?a)) => rewrite (Fopp_involutive f a); idtac "rewrite (Fopp_involutive" f a ")."
  | (Fopp f (FO f)) => rewrite (Fopp_O f); idtac "rewrite (Fopp_O" f ")."
  | (Fmul f (FO f) ?a) => rewrite (Fmul_O_l f a); idtac "rewrite (Fmul_O_l" f a ")."
  | (Fmul f ?a (FO f)) => rewrite (Fmul_O_r f a); idtac "rewrite (Fmul_O_r" f a ")."
  | (Fmul f (FI f) ?a) => rewrite (Fmul_I_l f a); idtac "rewrite (Fmul_I_l" f a ")."
  | (Fmul f ?a (FI f)) => rewrite (Fmul_I_r f a); idtac "rewrite (Fmul_I_r" f a ")."
  | (Fadd f (FO f) ?a) => rewrite (Fadd_O_l f a); idtac "rewrite (Fadd_O_l" f a ")."
  | (Fadd f ?a (FO f)) => rewrite (Fadd_O_r f a); idtac "rewrite (Fadd_O_r" f a ")."
  | (Fopp f (Fadd f ?a ?b)) => rewrite (Fopp_add_distr f a b); idtac "rewrite (Fopp_add_distr" f a b ")."
  | (Fmul f ?a (Fadd f ?b ?c)) => rewrite (Fmul_add_distr_l f a b c); idtac "rewrite (Fmul_add_distr_l" f a b c ")."
  | (Fmul f (Fadd f ?a ?b) ?c) => rewrite (Fmul_add_distr_r f a b c); idtac "rewrite (Fmul_add_distr_r" f a b c ")."
  | (Fopp f ?a) => eliminate_distr_F f a
  | (Fadd f ?a ?b) => eliminate_distr_F f a
  | (Fadd f ?a ?b) => eliminate_distr_F f b
  | (Fmul f ?a ?b) => eliminate_distr_F f a
  | (Fmul f ?a ?b) => eliminate_distr_F f b
end.

Ltac assoc_normalize_add_expression_F f expression := match expression with
  | (Fadd f ?a ?b) => match a with
    | (Fadd f ?d ?e) => rewrite (Fadd_assoc f d e b); idtac "rewrite (Fadd_assoc" f d e b ")."
    | _ => assoc_normalize_add_expression_F f b
  end
end.

Ltac put_out_opp_each_monomial_F f expression := match expression with
  | (Fadd f ?a ?b) => put_out_opp_each_monomial_F f a
  | (Fadd f ?a ?b) => put_out_opp_each_monomial_F f b
  | (Fopp f (Fopp f ?a)) => rewrite (Fopp_involutive f a); idtac "rewrite (Fopp_involutive" f a ")."
  | (Fopp f ?a) => put_out_opp_each_monomial_F f a
  | (Fmul f (FI f) ?a) => rewrite (Fmul_I_l f a); idtac "rewrite (Fmul_I_l" f a ")."
  | (Fmul f ?a (FI f)) => rewrite (Fmul_I_r f a); idtac "rewrite (Fmul_I_r" f a ")."
  | (Fmul f ?a ?b) => put_out_opp_each_monomial_F f a
  | (Fmul f ?a ?b) => put_out_opp_each_monomial_F f b
  | (Fmul f (Fopp f ?a) (Fopp f ?b)) => rewrite (Fmul_opp_opp f a b); idtac "rewrite (Fmul_opp_opp" f a b ")."
  | (Fmul f ?a (Fopp f ?b)) => rewrite (Fopp_mul_distr_r_reverse f a b); idtac "rewrite (Fopp_mul_distr_r_reverse" f a b ")."
  | (Fmul f (Fopp f ?a) ?b) => rewrite (Fopp_mul_distr_l_reverse f a b); idtac "rewrite (Fopp_mul_distr_l_reverse" f a b ")."
end.

Ltac assoc_normalize_mul_expression_F f expression := match expression with
  | (Fmul f ?a ?b) => match a with
    | (Fmul f ?d ?e) => rewrite (Fmul_assoc f d e b); idtac "rewrite (Fmul_assoc" f d e b ")."
    | _ => assoc_normalize_mul_expression_F f b
  end
  | (Fopp f ?a) => assoc_normalize_mul_expression_F f a
  | (Fadd f ?a ?b) => assoc_normalize_mul_expression_F f a
  | (Fadd f ?a ?b) => assoc_normalize_mul_expression_F f b
end.

Ltac move_to_first_mul_F f var expression := match expression with
  | (Fmul f ?a var) =>
    rewrite (Fmul_comm f a var);
    idtac "rewrite (Fmul_comm" f a var ")."
  | (Fmul f ?a (Fmul f var ?b)) =>
    rewrite - (Fmul_assoc f a var b); 
    idtac "rewrite - (Fmul_assoc" f a var b ").";
    rewrite (Fmul_comm f a var);
    idtac "rewrite (Fmul_comm" f a var ").";
    rewrite (Fmul_assoc f var a); 
    idtac "rewrite (Fmul_assoc" f var a ")."
  | (Fmul f ?a ?b) => move_to_first_mul_F f var b
end.

Ltac equalize_mul_F f a b := match a with
  | (Fopp f ?a1) => match b with
    | (Fopp f ?b1) => equalize_mul_F f a1 b1
  end
  | (Fmul f ?a1 ?a2) => match b with
    | (Fmul f a1 ?b2) => equalize_mul_F f a2 b2
    | _ => move_to_first_mul_F f a1 b
  end
end.

Ltac compare_term_sub_F f a b1 b2 arg2 arg3 := match a with
  | _ => match b1 with 
    | a => match b2 with
      | (FI f) => equalize_mul_F f arg2 arg3
    end
  end
  | (Fmul f ?a1 ?a2) => match b1 with
    | a1 => compare_term_sub_F f a2 b2 (FI f) arg2 arg3
    | (Fmul f ?b11 ?b12) => lazymatch b11 with
      | a1 => lazymatch b2 with 
         | (FI f) => compare_term_sub_F f a2 b12 (FI f) arg2 arg3
         | (FI f) => fail
         | _ => compare_term_sub_F f a2 (Fmul f b12 b2) (FI f) arg2 arg3
      end
      | (Fmul f ?b111 ?b112) => compare_term_sub_F f a (Fmul f b111 (Fmul f b112 b12)) b2 arg2 arg3
      | (Fmul f ?b111 ?b112) => fail
      | _ => lazymatch b2 with 
         | (FI f) => compare_term_sub_F f a b12 b11 arg2 arg3
         | (FI f) => fail
         | _ => compare_term_sub_F f a b12 (Fmul f b11 b2) arg2 arg3
      end
    end
  end
end.

Ltac compare_term_F f a b arg2 arg3 := match a with
  | (Fopp f ?a1) => match b with
    | (Fopp f ?b1) => compare_term_F f a1 b1 arg2 arg3
  end
  | _ => compare_term_sub_F f a b (FI f) arg2 arg3
end.

Ltac move_to_first_add_F f var expression := match expression with
  | (Fadd f ?a var) =>
    rewrite (Fadd_comm f a var);
    idtac "rewrite (Fadd_comm" f a var ")."
  | (Fadd f ?a (Fadd f var ?b)) =>
    rewrite - (Fadd_assoc f a var b); 
    idtac "rewrite - (Fadd_assoc" f a var b ").";
    rewrite (Fadd_comm f a var);
    idtac "rewrite (Fadd_comm" f a var ").";
    rewrite (Fadd_assoc f var a); 
    idtac "rewrite (Fadd_assoc" f var a ")."
  | (Fadd f ?a ?b) => move_to_first_add_F f var b
end.

Ltac include_same_term_F f var expression := match expression with
  | (Fadd f ?a ?b) => compare_term_F f var a var a
  | (Fadd f ?a ?b) => include_same_term_F f var b
  | _ => lazymatch expression with
    | (Fadd f ?a ?b) => fail
    | _ => compare_term_F f var expression var expression
  end
end.

Ltac include_term_F f var expression arg := match expression with
  | var => move_to_first_add_F f var arg
  | (Fadd f var ?b) => move_to_first_add_F f var arg
  | (Fadd f ?a ?b) => include_term_F f var b arg
end.

Ltac eliminate_opp_F f expression := match expression with
  | (Fadd f (Fopp f ?a) ?a) => rewrite (Fadd_opp_l f a); idtac "rewrite (Fadd_opp_l" f a ")."
  | (Fadd f ?a (Fopp f ?a)) => rewrite (Fadd_opp_r f a); idtac "rewrite (Fadd_opp_r" f a ")."
  | (Fadd f (Fopp f ?a) (Fadd f ?a ?b)) => rewrite - (Fadd_assoc f (Fopp f a) a b); idtac "rewrite - (Fadd_assoc" f "(Fopp" f a ")" a b ").";
    rewrite (Fadd_opp_l f a); idtac "rewrite (Fadd_opp_l" f a ").";
    rewrite (Fadd_O_l f b); idtac "rewrite (Fadd_O_l" f b ")."
  | (Fadd f ?a (Fadd f (Fopp f ?a) ?b)) => rewrite - (Fadd_assoc f a (Fopp f a) b); idtac "rewrite - (Fadd_assoc" f a "(Fopp" f a ")" b ").";
    rewrite (Fadd_opp_r f a); idtac "rewrite (Fadd_opp_r" f a ").";
    rewrite (Fadd_O_l f b); idtac "rewrite (Fadd_O_l" f b ")."
  | (Fadd f (Fopp f ?a) ?b) => include_term_F f a b b
  | (Fadd f (Fopp f ?a) ?b) => include_same_term_F f a b
  | (Fadd f ?a ?b) => include_term_F f (Fopp f a) b b
  | (Fadd f ?a ?b) => include_same_term_F f (Fopp f a) b
end.

Ltac equal_F f := repeat match goal with
  | [|- ?a = ?b] => eliminate_distr_F f a
end; repeat match goal with
  | [|- ?a = ?b] => eliminate_distr_F f b
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_add_expression_F f a
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_add_expression_F f b
end; repeat match goal with
  | [|- ?a = ?b] => put_out_opp_each_monomial_F f a
end; repeat match goal with
  | [|- ?a = ?b] => put_out_opp_each_monomial_F f b
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_mul_expression_F f a
end; repeat match goal with
  | [|- ?a = ?b] => assoc_normalize_mul_expression_F f b
end; repeat match goal with
  | _ => reflexivity; idtac "reflexivity."
  | [|- Fadd f ?a ?b = Fadd f ?a ?c] => apply (Fadd_eq_compat_l f a b c); idtac "apply (Fadd_eq_compat_l" f a b c ")."
  | [|- ?a = ?b] => eliminate_opp_F f a
  | [|- ?a = ?b] => eliminate_opp_F f b
  | [|- Fadd f ?a ?b = ?c] => include_term_F f a c c
  | [|- Fadd f ?a ?b = ?c] => include_same_term_F f a c
  | [|- Fopp f ?a = Fopp f ?b] => equalize_mul_F f a b
  | [|- ?a = ?b] => equalize_mul_F f a b
end.
