import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients
import OAI.RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart

/-! # Section Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.SectionCoefficients

noncomputable section

/-! Regular functions on the actual affine base change by dual numbers
have unique regular constant and first-order coefficients. Their native
dual-point values evaluate exactly these regular coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

theorem dualTensorCoefficients_evaluation {R : Type} [CommRing R] [Algebra ℂ R]
    (p : R →ₐ[ℂ] ℂ) (u : DualNumber ℂ ⊗[ℂ] R) :
    RepresentationTheory.Theta.Geometric.Dual.TensorEvaluation.dualTensorEvaluation p u = Dual.NumberCoefficients.dualNumberAlgMap p (Dual.NumberCoefficients.dualTensorCoefficients ℂ R u) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | tmul c a =>
    rw [Dual.NumberCoefficients.dualTensorCoefficients_tmul]
    apply TrivSqZeroExt.ext
    · rw [RepresentationTheory.Theta.Geometric.Dual.TensorEvaluation.dualTensorEvaluation_tmul_fst]
      exact (map_smul p c.fst a).symm
    · rw [RepresentationTheory.Theta.Geometric.Dual.TensorEvaluation.dualTensorEvaluation_tmul_snd]
      exact (map_smul p c.snd a).symm

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]

instance dualAffineSectionChart_isIso : IsIso (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualAffineBaseChangeChart X) := by
  exact ((pullbackSpecIso ℂ (DualNumber ℂ) Γ(X.left, ⊤)).symm ≪≫
    (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso
      (asIso (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv))).isIso_hom

def dualAffineSectionCoefficients :
    Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤) ≃+* DualNumber Γ(X.left, ⊤) := by
  letI : IsIso (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualAffineBaseChangeChart X).appTop :=
    inferInstanceAs (IsIso (Scheme.Γ.map (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualAffineBaseChangeChart X).op))
  exact (asIso (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualAffineBaseChangeChart X).appTop ≪≫
    Scheme.ΓSpecIso (.of (DualNumber ℂ ⊗[ℂ] Γ(X.left, ⊤)))).commRingCatIsoToRingEquiv.trans
      (Dual.NumberCoefficients.dualTensorCoefficientEquiv ℂ Γ(X.left, ⊤)).toRingEquiv

theorem dualAffineSectionCoefficients_apply (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤)) :
    dualAffineSectionCoefficients X s = Dual.NumberCoefficients.dualTensorCoefficients ℂ Γ(X.left, ⊤)
      ((Scheme.ΓSpecIso (.of (DualNumber ℂ ⊗[ℂ] Γ(X.left, ⊤)))).hom
        ((RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualAffineBaseChangeChart X).appTop s)) := rfl

theorem dualAffineSectionCoefficients_evaluation (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, ⊤)) :
    RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation.dualGlobalSectionValue (RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint X p).left s =
      Dual.NumberCoefficients.dualNumberAlgMap (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p) (dualAffineSectionCoefficients X s) := by
  rw [RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart.dualConstantPoint_sectionValue]
  exact dualTensorCoefficients_evaluation _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.SectionCoefficients
