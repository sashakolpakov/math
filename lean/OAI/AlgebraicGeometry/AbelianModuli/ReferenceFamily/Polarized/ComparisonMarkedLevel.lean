import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparisonLevel
import OAI.RepresentationTheory.Theta.Geometric.PresentedLevelComparison
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.RationalExponential
import OAI.RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport

/-! # Comparison Marked Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.ComparisonMarkedLevel

noncomputable section

/-! Exact exponential labels and their rational period comparison give
the full ordered-level equation on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {g N : ℕ} {δ : Fin g → ℕ}
    {A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase}
    (D : RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparison.NativePolarizedComparison A B)

def polarizedNativeLevelPoint (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)).toOver :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.abelian (Projectivity.polarizedNativeProjectivePresentation A)).inv
    ((A.level.hom.app (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))) (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase c)).val

theorem polarizedNativeLevelPoint_pullback {S : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    polarizedNativeLevelPoint (Q.pullback y.left) c =
      RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport.presentedFullLevelPoint Q.level y (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation Q y) c := rfl

theorem polarizedComparison_level_of_rational_labels {I : Type*}
    (label : I → Multiplicative (Fin (2 * g) → ZMod N)) (hlabel : Function.Surjective label)
    (v : I → Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)))
    (w : I → Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B))) (r : ℝ)
    (hv : ∀ i, polarizedNativeLevelPoint A (label i) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)).toOver)
        (r • (v i).val))
    (hw : ∀ i, polarizedNativeLevelPoint B (label i) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B)).toOver)
        (r • (w i).val))
    (hperiod : ∀ i, D.periods (v i) = w i)
    (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    (A.level.hom.app (.op T) c).val ≫ D.algebraicIso.hom = (B.level.hom.app (.op T) c).val := by
  let PA := RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation A
  let PB := RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation B
  have : IsMonHom D.algebraicIso.hom := D.algebraicIso_group
  apply RepresentationTheory.Theta.Geometric.PresentedLevelComparison.original_level_comparison_of_presented_points PA PB A.level B.level D.algebraicIso.hom ?_ T c
  intro t
  obtain ⟨i, rfl⟩ := hlabel t
  let j := (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.abelian (Projectivity.polarizedNativeProjectivePresentation A)).hom ≫
    D.algebraicIso.hom ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B.abelian (Projectivity.polarizedNativeProjectivePresentation B)).inv
  have : IsMonHom j := inferInstance
  have hp : Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift j (v i) = w i :=
    (LinearMap.congr_fun D.algebraicIso_rational (v i)).trans (hperiod i)
  exact RepresentationTheory.Theta.Geometric.Intrinsic.RationalExponential.nativeMap_point_of_rational_exp j r (v i) (w i)
    (polarizedNativeLevelPoint A (label i)) (polarizedNativeLevelPoint B (label i)) (hv i) (hw i) hp

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.ComparisonMarkedLevel
