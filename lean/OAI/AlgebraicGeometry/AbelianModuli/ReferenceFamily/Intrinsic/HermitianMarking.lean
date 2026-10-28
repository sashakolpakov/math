import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RosatiForm
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Matrices

/-! # Hermitian Marking -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking

noncomputable section

/-! Mark the actual native polarization form in E cubed and reconstruct
its E-Hermitian matrix through the nondegenerate field trace. Rosati
balance is proved from the Poincare bundle, not supplied as an input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Matrices.TraceReconstruction

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

def markedPolarizationForm : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] ℚ := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let e := PELMarking.IntrinsicPELMarking.coordinates A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ s hs hg hdegree
  exact (ChernPairing.nativePolarizationForm A).compl₁₂ (e.symm.restrictScalars ℚ).toLinearMap (e.symm.restrictScalars ℚ).toLinearMap

omit [NumberField.IsCMField E] in
theorem markedPolarizationForm_alternating (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : markedPolarizationForm A ρ s hs hg hdegree x x = 0 :=
  ChernPairing.nativePolarizationForm_alternating A _

theorem markedPolarizationForm_rosati (hρ : ActionData.RosatiConjugation A ρ) :
    Hermitian.Reconstruction.TraceReconstruction.RosatiBalanced (E := E) (markedPolarizationForm A ρ s hs hg hdegree) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let e := PELMarking.IntrinsicPELMarking.coordinates A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ s hs hg hdegree
  intro a x y
  change ChernPairing.nativePolarizationForm A (e.symm (a • x)) (e.symm y) =
    ChernPairing.nativePolarizationForm A (e.symm x) (e.symm (ComplexMultiplication.CM.TraceForm.cmFieldConjugation E a • y))
  rw [e.symm.map_smul, e.symm.map_smul]
  exact RosatiForm.nativePolarizationForm_rosati A ρ hρ a (e.symm x) (e.symm y)

def markedHermitianMatrix (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) : Matrix (Fin 3) (Fin 3) E :=
  Hermitian.Matrices.TraceReconstruction.hermitianMatrix ξ (markedPolarizationForm A ρ s hs hg hdegree)
    (markedPolarizationForm_rosati A ρ s hs hg hdegree hρ)

theorem markedHermitianMatrix_symmetry (hρ : ActionData.RosatiConjugation A ρ)
    (ξ : E) (hξ : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ) (i j : Fin 3) :
    markedHermitianMatrix A ρ s hs hg hdegree hρ ξ i j =
      ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (markedHermitianMatrix A ρ s hs hg hdegree hρ ξ j i) :=
  Hermitian.Matrices.TraceReconstruction.hermitianMatrix_symmetry ξ hξ (markedPolarizationForm A ρ s hs hg hdegree)
    (markedPolarizationForm_rosati A ρ s hs hg hdegree hρ)
    (markedPolarizationForm_alternating A ρ s hs hg hdegree) i j

theorem markedHermitianMatrix_trace (hρ : ActionData.RosatiConjugation A ρ)
    (ξ : E) (hξ : ξ ≠ 0) (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Algebra.trace ℚ E (ξ * ∑ i, ∑ j,
      x i * markedHermitianMatrix A ρ s hs hg hdegree hρ ξ i j * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (y j)) =
        markedPolarizationForm A ρ s hs hg hdegree x y := by
  have h := Hermitian.Matrices.TraceReconstruction.hermitianMatrix_evaluate ξ (markedPolarizationForm A ρ s hs hg hdegree)
    (markedPolarizationForm_rosati A ρ s hs hg hdegree hρ) x y
  exact (congrArg (fun z => Algebra.trace ℚ E (ξ * z)) h).trans
    (Hermitian.Reconstruction.TraceReconstruction.hermitianCoefficient_trace ξ hξ (markedPolarizationForm A ρ s hs hg hdegree) x y)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking
