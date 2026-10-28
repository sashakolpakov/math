import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionOpens
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConstantPointNaturality

/-! # Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Scalars

noncomputable section

/-! The native dual-number scalar acts on the actual family,
fixing its reduced scheme and every underlying open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem dualNumberScalar_origin (c : ℂ) : LieRanks.dualNumberOrigin ℂ ≫ LieRanks.dualNumberScalar ℂ c = LieRanks.dualNumberOrigin ℂ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (LieRanks.dualNumberReduction ℂ)) ≫
    Spec.map (CommRingCat.ofHom (LieRanks.dualNumberScale ℂ c).toRingHom) = Spec.map (CommRingCat.ofHom (LieRanks.dualNumberReduction ℂ))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun x => TrivSqZeroExt.fst_map _ x)

def dualFamilyScalar (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : ℂ) : LieRanks.dualNumberTest ℂ ⊗ X ⟶ LieRanks.dualNumberTest ℂ ⊗ X :=
  LieRanks.dualNumberScalar ℂ c ⊗ₘ 𝟙 X

theorem dualFamilyScalar_reduction (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : ℂ) :
    RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X ≫ dualFamilyScalar X c = RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [dualFamilyScalar, RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction, dualNumberScalar_origin]

theorem dualFamilyScalar_point (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : ℂ) (x : (LieRanks.dualNumberTest ℂ ⊗ X).left) :
    (dualFamilyScalar X c).left x = x := by
  obtain ⟨y, rfl⟩ := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction_surjective X).surj x
  exact congrArg (fun f : X ⟶ LieRanks.dualNumberTest ℂ ⊗ X => f.left y) (dualFamilyScalar_reduction X c)

theorem dualFamilyScalar_preimage (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : ℂ) (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) :
    (dualFamilyScalar X c).left ⁻¹ᵁ U = U := by
  ext x
  change (dualFamilyScalar X c).left x ∈ U ↔ x ∈ U
  rw [dualFamilyScalar_point]

theorem dualConstantPoint_scalar (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : ℂ) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p ≫ dualFamilyScalar X c = LieRanks.dualNumberScalar ℂ c ≫ RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint, dualFamilyScalar]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Scalars
