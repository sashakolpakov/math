import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes

/-! # Associative Parameters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameters.Construction

noncomputable section

/-! The universal six points for the associativity equation: three
independent group coordinates and one common fixed coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

variable {S : Scheme.{u}} (G X : Over S)

abbrev lineAssociativeParameter : Over S := ((G ⊗ G) ⊗ G) ⊗ X

abbrev lineAssociativeCoordinate1 : lineAssociativeParameter G X ⟶ G :=
  fst ((G ⊗ G) ⊗ G) X ≫ fst (G ⊗ G) G ≫ fst G G

abbrev lineAssociativeCoordinate2 : lineAssociativeParameter G X ⟶ G :=
  fst ((G ⊗ G) ⊗ G) X ≫ fst (G ⊗ G) G ≫ snd G G

abbrev lineAssociativeCoordinate3 : lineAssociativeParameter G X ⟶ G :=
  fst ((G ⊗ G) ⊗ G) X ≫ snd (G ⊗ G) G

abbrev lineAssociativeFixed : lineAssociativeParameter G X ⟶ X := snd ((G ⊗ G) ⊗ G) X

def lineAssociativePoint1 : lineAssociativeParameter G X ⟶ G ⊗ X :=
  lift (lineAssociativeCoordinate1 G X) (lineAssociativeFixed G X)

def lineAssociativePoint2 : lineAssociativeParameter G X ⟶ G ⊗ X :=
  lift (lineAssociativeCoordinate2 G X) (lineAssociativeFixed G X)

def lineAssociativePoint3 : lineAssociativeParameter G X ⟶ G ⊗ X :=
  lift (lineAssociativeCoordinate3 G X) (lineAssociativeFixed G X)

instance lineAssociativePoint1_isMonHom [GrpObj G] [GrpObj X] : IsMonHom (lineAssociativePoint1 G X) := by
  unfold lineAssociativePoint1
  infer_instance

instance lineAssociativePoint2_isMonHom [GrpObj G] [GrpObj X] : IsMonHom (lineAssociativePoint2 G X) := by
  unfold lineAssociativePoint2
  infer_instance

instance lineAssociativePoint3_isMonHom [GrpObj G] [GrpObj X] : IsMonHom (lineAssociativePoint3 G X) := by
  unfold lineAssociativePoint3
  infer_instance

variable [GrpObj G]

def lineAssociativePoint12 : lineAssociativeParameter G X ⟶ G ⊗ X :=
  lift (lineAssociativeCoordinate1 G X * lineAssociativeCoordinate2 G X) (lineAssociativeFixed G X)

def lineAssociativePoint23 : lineAssociativeParameter G X ⟶ G ⊗ X :=
  lift (lineAssociativeCoordinate2 G X * lineAssociativeCoordinate3 G X) (lineAssociativeFixed G X)

def lineAssociativePoint123 : lineAssociativeParameter G X ⟶ G ⊗ X :=
  lift ((lineAssociativeCoordinate1 G X * lineAssociativeCoordinate2 G X) * lineAssociativeCoordinate3 G X)
    (lineAssociativeFixed G X)

theorem lineAssociativeRelation12 : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X)
    (lineAssociativePoint1 G X) (lineAssociativePoint2 G X) (lineAssociativePoint12 G X) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lineAssociativePoint1, lineAssociativePoint2, lineAssociativePoint12, lift_fst, lift_snd]

theorem lineAssociativeRelation23 : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X)
    (lineAssociativePoint2 G X) (lineAssociativePoint3 G X) (lineAssociativePoint23 G X) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lineAssociativePoint2, lineAssociativePoint3, lineAssociativePoint23, lift_fst, lift_snd]

theorem lineAssociativeRelation1_23 : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X)
    (lineAssociativePoint1 G X) (lineAssociativePoint23 G X) (lineAssociativePoint123 G X) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lineAssociativePoint1, lineAssociativePoint23, lineAssociativePoint123, lift_fst, lift_snd, mul_assoc]

theorem lineAssociativeRelation12_3 : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X)
    (lineAssociativePoint12 G X) (lineAssociativePoint3 G X) (lineAssociativePoint123 G X) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lineAssociativePoint12, lineAssociativePoint3, lineAssociativePoint123, lift_fst, lift_snd]

local instance lineAssociativeMapMul_isMonHom {T B : Over S} [GrpObj T] [GrpObj B] [IsCommMonObj B]
    (a b : T ⟶ B) [IsMonHom a] [IsMonHom b] : IsMonHom (a * b) := by
  rw [Hom.mul_def]
  infer_instance

variable [GrpObj X] [IsCommMonObj G]

instance lineAssociativePoint12_isMonHom : IsMonHom (lineAssociativePoint12 G X) := by
  unfold lineAssociativePoint12
  infer_instance

instance lineAssociativePoint23_isMonHom : IsMonHom (lineAssociativePoint23 G X) := by
  unfold lineAssociativePoint23
  infer_instance

instance lineAssociativePoint123_isMonHom : IsMonHom (lineAssociativePoint123 G X) := by
  unfold lineAssociativePoint123
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameters.Construction
