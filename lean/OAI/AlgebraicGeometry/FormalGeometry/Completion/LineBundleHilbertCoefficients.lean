import OAI.AlgebraicGeometry.FormalGeometry.Completion.CokernelTensorTopCoefficient
import OAI.AlgebraicGeometry.FormalGeometry.Completion.EffectiveHilbertDifference
import OAI.AlgebraicGeometry.FormalGeometry.Completion.TensorSectionMap

/-! # Line Bundle Hilbert Coefficients -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleHilbertCoefficients

noncomputable section

/-! Coefficients of actual line-bundle Hilbert differences are additive
when a generated factor has no higher-degree contribution. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Polynomial

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

def lineBundleHilbertCoefficient (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) (d : ℕ) : ℚ :=
  (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f L j).coeff d

omit [IsIntegral X] in
theorem lineBundleHilbertPolynomial_iso (L B : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (e : L.sheaf ≅ B.sheaf) (j : Fin (r + 1)) :
    EffectiveHilbertDifference.Construction.lineBundleHilbertPolynomial f L j = EffectiveHilbertDifference.Construction.lineBundleHilbertPolynomial f B j := by
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
  have : B.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent B
  have : B.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation B
  exact ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_iso f e j

omit [IsIntegral X] in
theorem lineBundleHilbertCoefficient_iso (L B : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (e : L.sheaf ≅ B.sheaf) (j : Fin (r + 1)) (d : ℕ) :
    lineBundleHilbertCoefficient f L j d = lineBundleHilbertCoefficient f B j d := by
  unfold lineBundleHilbertCoefficient EffectiveHilbertDifference.Construction.lineBundleHilbertDifference
  rw [lineBundleHilbertPolynomial_iso f L B e j]

theorem lineBundleHilbertCoefficient_tensor_generated_left [Infinite K]
    (B L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hB : Frame.SectionDetection.Construction.HasFrameSections B.sheaf) (j : Fin (r + 1)) (d : ℕ)
    (hd : (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f B j).natDegree ≤ d) :
    lineBundleHilbertCoefficient f (B.tensor L) j d =
      lineBundleHilbertCoefficient f B j d + lineBundleHilbertCoefficient f L j d := by
  have : B.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent B
  have : B.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation B
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
  have : (B.tensor L).sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (B.tensor L)
  have : (B.tensor L).sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation (B.tensor L)
  have : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  have : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  obtain ⟨s, hs⟩ := hB (genericPoint X)
  have : Mono s := IntegralSectionMono.Construction.integral_section_mono_of_nonempty_nonvanishing s ⟨genericPoint X, hs⟩
  have hC : ClosedHilbertAdditivity.Construction.closedProjectiveCokernelHilbertPolynomial f s j = EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f B j :=
    ClosedHilbertAdditivity.Construction.closedProjectiveCokernelHilbertPolynomial_eq_sub f s j
  have hc := CokernelTensorTopCoefficient.Construction.coherentCokernelTensor_coeff_eq f s L j d (hC.symm ▸ hd)
  have hBL : ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor B.sheaf L) j =
      EffectiveHilbertDifference.Construction.lineBundleHilbertPolynomial f (B.tensor L) j :=
    ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_iso f (M := CoherentLineBundleTensor.Construction.coherentLineBundleTensor B.sheaf L)
      (N := (B.tensor L).sheaf) (Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.tensorIso B.sheaf L.sheaf) j
  have hOL : ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) L) j =
      EffectiveHilbertDifference.Construction.lineBundleHilbertPolynomial f L j :=
    ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_iso f (M := CoherentLineBundleTensor.Construction.coherentLineBundleTensor (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) L)
      (N := L.sheaf) (TensorSectionMap.Construction.structureLeftUnitor L.sheaf) j
  rw [hBL, hOL] at hc
  change (EffectiveHilbertDifference.Construction.lineBundleHilbertPolynomial f (B.tensor L) j - EffectiveHilbertDifference.Construction.lineBundleHilbertPolynomial f L j).coeff d =
    (EffectiveHilbertDifference.Construction.lineBundleHilbertDifference f B j).coeff d at hc
  unfold lineBundleHilbertCoefficient EffectiveHilbertDifference.Construction.lineBundleHilbertDifference at *
  simp only [coeff_sub] at *
  linarith

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleHilbertCoefficients
