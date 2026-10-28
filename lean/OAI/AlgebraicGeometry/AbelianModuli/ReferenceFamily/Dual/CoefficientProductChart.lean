import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ProductProjections

/-! # Coefficient Product Chart -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientProductChart

noncomputable section

/-! The original coefficient scheme of an affine dual-number chart
is the actual product with the dual-number test. The isomorphism has
the literal coefficient-extension and projection maps as projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver LieRanks.dualNumberTest

variable (B : CommAlgCat ℂ)

def dualCoefficientProductMap : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B) ⟶ LieRanks.dualNumberTest ℂ ⊗ EtaleSplittingAt.EtaleSplitting.affineOver ℂ B :=
  lift (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber ℂ) (DualNumber B) (NumberCoefficients.dualNumberAlgMap (Algebra.ofId ℂ B)))
    (CoefficientSchemeTests.dualCoefficientProjection ℂ B)

theorem dualCoefficientProductMap_left :
    (dualCoefficientProductMap B).left =
      Spec.map (CommRingCat.ofHom (NumberCoefficients.dualTensorCoefficients ℂ B).toRingHom) ≫
        (pullbackSpecIso ℂ (DualNumber ℂ) B).inv := by
  apply pullback.hom_ext
  · have h := HilbertConstruction.Affine.ProductProjections.affineProductComparison_fst ℂ (DualNumber ℂ) B (DualNumber B) (NumberCoefficients.dualTensorCoefficients ℂ B)
    have he : (NumberCoefficients.dualTensorCoefficients ℂ B).comp (Algebra.TensorProduct.includeLeft (S := ℂ)) =
        NumberCoefficients.dualNumberAlgMap (Algebra.ofId ℂ B) := Algebra.TensorProduct.lift_comp_includeLeft _ _ _
    rw [he] at h
    exact (congrArg Over.Hom.left (lift_fst _ _)).trans h.symm
  · have h := HilbertConstruction.Affine.ProductProjections.affineProductComparison_snd ℂ (DualNumber ℂ) B (DualNumber B) (NumberCoefficients.dualTensorCoefficients ℂ B)
    have he : (NumberCoefficients.dualTensorCoefficients ℂ B).comp Algebra.TensorProduct.includeRight =
        TrivSqZeroExt.inlAlgHom ℂ B B := Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)
    rw [he] at h
    exact (congrArg Over.Hom.left (lift_snd _ _)).trans h.symm

def dualCoefficientProductSchemeIso :
    (EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B)).left ≅ (LieRanks.dualNumberTest ℂ ⊗ EtaleSplittingAt.EtaleSplitting.affineOver ℂ B).left :=
  (Scheme.Spec.mapIso (NumberCoefficients.dualTensorCoefficientEquiv ℂ B).toRingEquiv.toCommRingCatIso.op) ≪≫
    (pullbackSpecIso ℂ (DualNumber ℂ) B).symm

theorem dualCoefficientProductMap_eq_iso :
    (dualCoefficientProductMap B).left = (dualCoefficientProductSchemeIso B).hom :=
  dualCoefficientProductMap_left B

instance dualCoefficientProductMap_isIso : IsIso (dualCoefficientProductMap B).left :=
  (dualCoefficientProductMap_eq_iso B).symm ▸ (dualCoefficientProductSchemeIso B).isIso_hom

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientProductChart
