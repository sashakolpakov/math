import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameters

/-! # Interchange Parameters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameters.Construction

noncomputable section

/-! The universal interchange square has two group coordinates in
each direction. Its nine points and six product relations are actual
maps on the product parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

variable {S : Scheme.{u}} (G X : Over S)

abbrev lineInterchangeParameter : Over S := (G ⊗ G) ⊗ (X ⊗ X)
abbrev lineInterchangeG1 : lineInterchangeParameter G X ⟶ G := fst (G ⊗ G) (X ⊗ X) ≫ fst G G
abbrev lineInterchangeG2 : lineInterchangeParameter G X ⟶ G := fst (G ⊗ G) (X ⊗ X) ≫ snd G G
abbrev lineInterchangeX1 : lineInterchangeParameter G X ⟶ X := snd (G ⊗ G) (X ⊗ X) ≫ fst X X
abbrev lineInterchangeX2 : lineInterchangeParameter G X ⟶ X := snd (G ⊗ G) (X ⊗ X) ≫ snd X X

def lineInterchangePointC : lineInterchangeParameter G X ⟶ G ⊗ X := lift (lineInterchangeG1 G X) (lineInterchangeX1 G X)
def lineInterchangePointA : lineInterchangeParameter G X ⟶ G ⊗ X := lift (lineInterchangeG1 G X) (lineInterchangeX2 G X)
def lineInterchangePointB : lineInterchangeParameter G X ⟶ G ⊗ X := lift (lineInterchangeG2 G X) (lineInterchangeX1 G X)
def lineInterchangePointX : lineInterchangeParameter G X ⟶ G ⊗ X := lift (lineInterchangeG2 G X) (lineInterchangeX2 G X)

variable [GrpObj G] [GrpObj X]

def lineInterchangePointCA : lineInterchangeParameter G X ⟶ G ⊗ X :=
  lift (lineInterchangeG1 G X) (lineInterchangeX1 G X * lineInterchangeX2 G X)
def lineInterchangePointCB : lineInterchangeParameter G X ⟶ G ⊗ X :=
  lift (lineInterchangeG1 G X * lineInterchangeG2 G X) (lineInterchangeX1 G X)
def lineInterchangePointAX : lineInterchangeParameter G X ⟶ G ⊗ X :=
  lift (lineInterchangeG1 G X * lineInterchangeG2 G X) (lineInterchangeX2 G X)
def lineInterchangePointBX : lineInterchangeParameter G X ⟶ G ⊗ X :=
  lift (lineInterchangeG2 G X) (lineInterchangeX1 G X * lineInterchangeX2 G X)
def lineInterchangePointW : lineInterchangeParameter G X ⟶ G ⊗ X :=
  lift (lineInterchangeG1 G X * lineInterchangeG2 G X) (lineInterchangeX1 G X * lineInterchangeX2 G X)

omit [GrpObj X] in
theorem lineInterchangeRelationAX : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X)
    (lineInterchangePointA G X) (lineInterchangePointX G X) (lineInterchangePointAX G X) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lineInterchangePointA, lineInterchangePointX, lineInterchangePointAX, lift_fst, lift_snd]

omit [GrpObj G] in
theorem lineInterchangeRelationBX : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd G X) (fst G X)
    (lineInterchangePointB G X) (lineInterchangePointX G X) (lineInterchangePointBX G X) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lineInterchangePointB, lineInterchangePointX, lineInterchangePointBX, lift_fst, lift_snd]

omit [GrpObj X] in
theorem lineInterchangeRelationCB : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X)
    (lineInterchangePointC G X) (lineInterchangePointB G X) (lineInterchangePointCB G X) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lineInterchangePointC, lineInterchangePointB, lineInterchangePointCB, lift_fst, lift_snd]

omit [GrpObj G] in
theorem lineInterchangeRelationCA : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd G X) (fst G X)
    (lineInterchangePointC G X) (lineInterchangePointA G X) (lineInterchangePointCA G X) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lineInterchangePointC, lineInterchangePointA, lineInterchangePointCA, lift_fst, lift_snd]

theorem lineInterchangeRelationBY : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd G X) (fst G X)
    (lineInterchangePointCB G X) (lineInterchangePointAX G X) (lineInterchangePointW G X) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lineInterchangePointCB, lineInterchangePointAX, lineInterchangePointW, lift_fst, lift_snd]

theorem lineInterchangeRelationAZ : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X)
    (lineInterchangePointCA G X) (lineInterchangePointBX G X) (lineInterchangePointW G X) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lineInterchangePointCA, lineInterchangePointBX, lineInterchangePointW, lift_fst, lift_snd]

attribute [local instance] AssociativeParameters.Construction.lineAssociativeMapMul_isMonHom

instance lineInterchangePointC_isMonHom : IsMonHom (lineInterchangePointC G X) := by
  unfold lineInterchangePointC
  infer_instance
instance lineInterchangePointA_isMonHom : IsMonHom (lineInterchangePointA G X) := by
  unfold lineInterchangePointA
  infer_instance
instance lineInterchangePointB_isMonHom : IsMonHom (lineInterchangePointB G X) := by
  unfold lineInterchangePointB
  infer_instance
instance lineInterchangePointX_isMonHom : IsMonHom (lineInterchangePointX G X) := by
  unfold lineInterchangePointX
  infer_instance
instance lineInterchangePointCA_isMonHom [IsCommMonObj X] : IsMonHom (lineInterchangePointCA G X) := by
  unfold lineInterchangePointCA
  infer_instance
instance lineInterchangePointCB_isMonHom [IsCommMonObj G] : IsMonHom (lineInterchangePointCB G X) := by
  unfold lineInterchangePointCB
  infer_instance
instance lineInterchangePointAX_isMonHom [IsCommMonObj G] : IsMonHom (lineInterchangePointAX G X) := by
  unfold lineInterchangePointAX
  infer_instance
instance lineInterchangePointBX_isMonHom [IsCommMonObj X] : IsMonHom (lineInterchangePointBX G X) := by
  unfold lineInterchangePointBX
  infer_instance
instance lineInterchangePointW_isMonHom [IsCommMonObj G] [IsCommMonObj X] : IsMonHom (lineInterchangePointW G X) := by
  unfold lineInterchangePointW
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameters.Construction
