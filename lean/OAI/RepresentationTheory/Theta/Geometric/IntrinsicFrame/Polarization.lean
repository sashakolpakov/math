import OAI.RepresentationTheory.Theta.Geometric.FrameDiagonalForm
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.ChernForm

/-! # Polarization -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original polarization form is locally constant in the same
constructed full period frame of the actual polarized abelian family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation PolarizedCanonicalForm.familyPolarizationForm AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.exists_constant_polarization_form (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C) :
    let P := fun z => PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)
    ∃ U : Set (Intrinsic.FamilyFrames.FamilyChartBase C), IsOpen U ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ U ∧
      ∃ (hU : U ⊆ F.neighborhood) (hN : U ⊆ C.charts.charts.neighborhood),
        ∀ (z : U) (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (P (Intrinsic.FamilyFrames.familyChartCenter C)).variety),
          PolarizedCanonicalForm.familyPolarizationForm A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) v w =
          PolarizedCanonicalForm.familyPolarizationForm A (Intrinsic.FamilyFrames.familyChartParameter C z)
            (F.nativeRationalTransport z (hU z.property) (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z) v)
            (F.nativeRationalTransport z (hU z.property) (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z) w) := by
  let P := fun z => PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)
  let L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S A.abelian).left := FrameDiagonalForm.familyPolarizationDiagonalLine A
  obtain ⟨U, hUopen, hxU, hU, hN, hform⟩ :=
    F.exists_constant_native_chern_form (PolarizedCanonicalForm.polarizedFamilyPresentation A) L
  refine ⟨U, hUopen, hxU, hU, hN, ?_⟩
  intro z v w
  have h₀ := FrameDiagonalForm.frameDiagonalForm A C (Intrinsic.FamilyFrames.familyChartCenter C) v w
  have hz := FrameDiagonalForm.frameDiagonalForm A C z
    (F.nativeRationalTransport z (hU z.property) (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z) v)
    (F.nativeRationalTransport z (hU z.property) (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z) w)
  have he := h₀.symm.trans ((hform z v w).trans hz)
  exact mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0) he

end

end OAI.RepresentationTheory.Theta.Geometric
