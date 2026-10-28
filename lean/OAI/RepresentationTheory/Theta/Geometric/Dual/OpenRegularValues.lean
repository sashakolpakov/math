import OAI.RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction
import OAI.RepresentationTheory.Theta.Geometric.Dual.OpenSectionValues
import OAI.RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart

/-! # Open Regular Values -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.OpenRegularValues

noncomputable section

/-! Values of regular sections on opens of a native dual-number base
change, evaluated at the actual constant dual-number points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem dualConstantPoint_open_range (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (U : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (hp : (BaseChangeReduction.dualBaseChangeReduction X).left (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈ U) :
    (⊤ : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ).left.Opens) ≤ (AffineBaseChangeChart.dualConstantPoint X p).left ⁻¹ᵁ U := by
  let : Subsingleton (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ).left := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberSpectrum.dualNumber_primeSpectrum_subsingleton
  intro t _
  have ht : t = (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) := Subsingleton.elim _ _
  have H := congrArg (fun f : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X =>
    f.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (BaseChangeReduction.dualConstantPoint_reduction X p)
  change (AffineBaseChangeChart.dualConstantPoint X p).left t ∈ U
  exact (congrArg (AffineBaseChangeChart.dualConstantPoint X p).left ht).trans H ▸ hp

def dualOpenRegularFunctionValue (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (U : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (s : Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, U)) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : DualNumber ℂ := by
  classical
  exact if hp : (BaseChangeReduction.dualBaseChangeReduction X).left (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈ U then
    OpenSectionValues.dualSectionValue (AffineBaseChangeChart.dualConstantPoint X p).left U (dualConstantPoint_open_range X p U hp) s else 0

theorem dualOpenRegularFunctionValue_of_mem (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (U : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (s : Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, U)) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hp : (BaseChangeReduction.dualBaseChangeReduction X).left (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈ U) :
    dualOpenRegularFunctionValue X U s p =
      OpenSectionValues.dualSectionValue (AffineBaseChangeChart.dualConstantPoint X p).left U (dualConstantPoint_open_range X p U hp) s := by
  classical
  exact dite_eq_left hp

theorem dualOpenRegularFunctionValue_pullback {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    (U : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens)
    (s : Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ Y).left, U))
    (hf : (⊤ : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) ≤
      (𝟙 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ U)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    dualOpenRegularFunctionValue Y U s (p ≫ f) =
      SectionEvaluation.dualGlobalSectionValue (AffineBaseChangeChart.dualConstantPoint X p).left
        ((𝟙 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.appLE U ⊤ hf s) := by
  have H := congrArg (fun g : X ⟶ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ Y =>
    g.left (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (BaseChangeReduction.dualBaseChangeReduction_natural f)
  have hp : (BaseChangeReduction.dualBaseChangeReduction Y).left ((p ≫ f).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈ U :=
    H ▸ (hf (show (BaseChangeReduction.dualBaseChangeReduction X).left (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈
      (⊤ : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) by trivial))
  rw [dualOpenRegularFunctionValue_of_mem Y U s (p ≫ f) hp]
  have hvalue := OpenSectionValues.dualSectionValue_pullback (AffineBaseChangeChart.dualConstantPoint X p).left
    (𝟙 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ f).left U ⊤ hf (by simp) s
  have hn := congrArg Over.Hom.left (AffineBaseChangeChart.dualConstantPoint_natural f p)
  exact (OpenSectionValues.dualSectionValue_congr _ _ hn U _ _ s).symm.trans
    (hvalue.symm.trans (OpenSectionValues.dualSectionValue_top _ _))

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.OpenRegularValues
