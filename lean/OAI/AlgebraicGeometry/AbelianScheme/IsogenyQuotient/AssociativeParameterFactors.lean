import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameters

/-! # Associative Parameter Factors -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameterFactors.Construction

noncomputable section

/-! Every actual test-scheme associativity configuration factors
through the universal parameter, with all six point equations proved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

variable {S : Scheme.{u}} {G X T : Over S}

def lineAssociativeParameterLift (a b c : T ⟶ G ⊗ X) : T ⟶ AssociativeParameters.Construction.lineAssociativeParameter G X :=
  lift (lift (lift (a ≫ fst G X) (b ≫ fst G X)) (c ≫ fst G X)) (a ≫ snd G X)

theorem lineAssociativeParameterLift_coordinate1 (a b c : T ⟶ G ⊗ X) :
    lineAssociativeParameterLift a b c ≫ AssociativeParameters.Construction.lineAssociativeCoordinate1 G X = a ≫ fst G X := by
  simp only [lineAssociativeParameterLift, AssociativeParameters.Construction.lineAssociativeCoordinate1, lift_fst_assoc, lift_fst]

theorem lineAssociativeParameterLift_coordinate2 (a b c : T ⟶ G ⊗ X) :
    lineAssociativeParameterLift a b c ≫ AssociativeParameters.Construction.lineAssociativeCoordinate2 G X = b ≫ fst G X := by
  simp only [lineAssociativeParameterLift, AssociativeParameters.Construction.lineAssociativeCoordinate2, lift_fst_assoc, lift_snd]

theorem lineAssociativeParameterLift_coordinate3 (a b c : T ⟶ G ⊗ X) :
    lineAssociativeParameterLift a b c ≫ AssociativeParameters.Construction.lineAssociativeCoordinate3 G X = c ≫ fst G X := by
  simp only [lineAssociativeParameterLift, AssociativeParameters.Construction.lineAssociativeCoordinate3, lift_fst_assoc, lift_snd]

theorem lineAssociativeParameterLift_fixed (a b c : T ⟶ G ⊗ X) :
    lineAssociativeParameterLift a b c ≫ AssociativeParameters.Construction.lineAssociativeFixed G X = a ≫ snd G X :=
  lift_snd _ _

theorem lineAssociativeParameterLift_point (a b c d : T ⟶ G ⊗ X)
    (v : AssociativeParameters.Construction.lineAssociativeParameter G X ⟶ G)
    (hv : lineAssociativeParameterLift a b c ≫ v = d ≫ fst G X) (h : a ≫ snd G X = d ≫ snd G X) :
    lineAssociativeParameterLift a b c ≫ lift v (AssociativeParameters.Construction.lineAssociativeFixed G X) = d := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, lift_fst] using hv
  · simpa only [Category.assoc, lift_snd, lineAssociativeParameterLift_fixed] using h

theorem lineAssociativeParameterLift_point1 (a b c : T ⟶ G ⊗ X) :
    lineAssociativeParameterLift a b c ≫ AssociativeParameters.Construction.lineAssociativePoint1 G X = a :=
  lineAssociativeParameterLift_point a b c a _ (lineAssociativeParameterLift_coordinate1 a b c) rfl

theorem lineAssociativeParameterLift_point2 (a b c : T ⟶ G ⊗ X) (h : a ≫ snd G X = b ≫ snd G X) :
    lineAssociativeParameterLift a b c ≫ AssociativeParameters.Construction.lineAssociativePoint2 G X = b :=
  lineAssociativeParameterLift_point a b c b _ (lineAssociativeParameterLift_coordinate2 a b c) h

theorem lineAssociativeParameterLift_point3 (a b c : T ⟶ G ⊗ X) (h : a ≫ snd G X = c ≫ snd G X) :
    lineAssociativeParameterLift a b c ≫ AssociativeParameters.Construction.lineAssociativePoint3 G X = c :=
  lineAssociativeParameterLift_point a b c c _ (lineAssociativeParameterLift_coordinate3 a b c) h

variable [GrpObj G]

theorem lineAssociativeParameterLift_point12 (a b c ab : T ⟶ G ⊗ X)
    (hab : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X) a b ab) :
    lineAssociativeParameterLift a b c ≫ AssociativeParameters.Construction.lineAssociativePoint12 G X = ab := by
  apply lineAssociativeParameterLift_point a b c ab _ _ hab.2.2
  rw [MonObj.comp_mul, lineAssociativeParameterLift_coordinate1, lineAssociativeParameterLift_coordinate2]
  exact hab.1

theorem lineAssociativeParameterLift_point23 (a b c bc : T ⟶ G ⊗ X)
    (hab : a ≫ snd G X = b ≫ snd G X) (hbc : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X) b c bc) :
    lineAssociativeParameterLift a b c ≫ AssociativeParameters.Construction.lineAssociativePoint23 G X = bc := by
  apply lineAssociativeParameterLift_point a b c bc _ _ (hab.trans hbc.2.2)
  rw [MonObj.comp_mul, lineAssociativeParameterLift_coordinate2, lineAssociativeParameterLift_coordinate3]
  exact hbc.1

theorem lineAssociativeParameterLift_point123 (a b c ab d : T ⟶ G ⊗ X)
    (hab : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X) a b ab) (hd : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X) ab c d) :
    lineAssociativeParameterLift a b c ≫ AssociativeParameters.Construction.lineAssociativePoint123 G X = d := by
  apply lineAssociativeParameterLift_point a b c d _ _ (hab.2.2.trans hd.2.2)
  simpa only [MonObj.comp_mul, lineAssociativeParameterLift_coordinate1,
    lineAssociativeParameterLift_coordinate2, lineAssociativeParameterLift_coordinate3, hab.1] using hd.1

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameterFactors.Construction
