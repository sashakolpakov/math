import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking

/-! # Hermitian Nondegenerate -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianNondegenerate.IntrinsicHermitianMarking

noncomputable section

/-! The matrix reconstructed from the actual polarized family has
nonzero determinant, by positivity of its original ample Chern class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

omit [NumberField.IsCMField E] in
theorem markedPolarizationForm_separating (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hx : ∀ y, HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm A ρ s hs hg hdegree x y = 0) : x = 0 := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let e := PELMarking.IntrinsicPELMarking.coordinates A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ s hs hg hdegree
  have hzero : e.symm x = 0 := by
    apply ChernPeriod.nativePolarizationForm_separating A
    intro y
    have h := hx (e y)
    change ChernPairing.nativePolarizationForm A (e.symm x) (e.symm (e y)) = 0 at h
    rw [e.symm_apply_apply] at h
    exact h
  exact e.symm.injective (hzero.trans e.symm.map_zero.symm)

theorem markedHermitianMatrix_det_ne_zero (hρ : ActionData.RosatiConjugation A ρ)
    (ξ : E) (hξ : ξ ≠ 0) :
    (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ).det ≠ 0 :=
  Hermitian.Matrices.TraceReconstruction.hermitianMatrix_det_ne_zero ξ hξ (HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm A ρ s hs hg hdegree)
    (HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm_rosati A ρ s hs hg hdegree hρ)
    (markedPolarizationForm_separating A ρ s hs hg hdegree)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianNondegenerate.IntrinsicHermitianMarking
