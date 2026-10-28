import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructurePullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoordinateComplexConstants

/-! # Structure Sheaf Scalar Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureSheafScalarPullback

noncomputable section

/-! The actual structure-sheaf pullback commutes with the complex
scalar endomorphisms defined by the original structure morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def structureAdditiveScalar (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : ℂ) :
    Dual.UnitCechClasses.ringAdditiveSheaf X.left.sheaf ⟶ Dual.UnitCechClasses.ringAdditiveSheaf X.left.sheaf :=
  (SheafOfModules.toSheaf X.left.ringCatSheaf).map
    (SheafCohomology.AffineH.Projective.globalSmulHom (HilbertConstruction.Line.Bundles.structureModule X.left) (Open.ComplexConstants.complexGlobalSectionMap X c))

theorem structureAdditiveScalar_app (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : ℂ) (U : X.left.Opens) (x : Γ(X.left, U)) :
    (structureAdditiveScalar X c).hom.app (.op U) x =
      X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (Open.ComplexConstants.complexGlobalSectionMap X c) * x := rfl

theorem structureAdditiveScalar_pullback {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : A ⟶ B) (c : ℂ) :
    structureAdditiveScalar B c ≫ StructurePullback.structureAdditivePullbackHom f.left =
      StructurePullback.structureAdditivePullbackHom f.left ≫
        (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f.left.base).map (structureAdditiveScalar A c) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  change Γ(B.left, U.unop) at x
  change f.left.app U.unop
      (B.left.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (Open.ComplexConstants.complexGlobalSectionMap B c) * x) =
    A.left.presheaf.map (homOfLE (show f.left ⁻¹ᵁ U.unop ≤ ⊤ from le_top)).op (Open.ComplexConstants.complexGlobalSectionMap A c) *
      f.left.app U.unop x
  rw [map_mul]
  have hn := ConcreteCategory.congr_hom
    (f.left.naturality (homOfLE (show U.unop ≤ ⊤ from le_top)).op) (Open.ComplexConstants.complexGlobalSectionMap B c)
  change f.left.app U.unop
      (B.left.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (Open.ComplexConstants.complexGlobalSectionMap B c)) =
    A.left.presheaf.map (homOfLE (show f.left ⁻¹ᵁ U.unop ≤ ⊤ from le_top)).op
      (f.left.appTop (Open.ComplexConstants.complexGlobalSectionMap B c)) at hn
  rw [Affine.CoordinateComplexConstants.complexGlobalSectionMap_natural] at hn
  rw [hn]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureSheafScalarPullback
