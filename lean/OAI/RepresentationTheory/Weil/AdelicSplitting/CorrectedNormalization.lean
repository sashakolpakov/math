import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedGeneratorKernels
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakCayleyCoefficients

/-! # Corrected Normalization -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction

noncomputable section

section

/-! Exact weak Heisenberg covariance of the corrected open-cell phase.
This identity is derived from translation of the actual Weyl coefficients,
without assuming an oscillator or a splitting over the symplectic matrix. -/

open _root_.MeasureTheory

variable (k : Type) [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (N : ℕ)

omit [CompleteSpace k] [LocallyCompactSpace k] [CharZero k] [MeasurableSpace k]
  [BorelSpace k] [SecondCountableTopology k] in
theorem schrodingerPairing_eq_standardBilinear :
    SchrodingerPairing.Construction.schrodingerPairing k N = UnitarySplitting.StandardTransvections.Construction.standardSymplecticBilinear k N := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact SchrodingerPairing.Construction.schrodingerPairing_eq_standard k N x y

def standardSymplecticOfMatrix (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) : UnitarySplitting.FrameTransport.Construction.StandardSymplectic k N :=
  ⟨SchrodingerPairing.Construction.symplecticPhaseEquiv k N g, fun x y => by
    change UnitarySplitting.Oscillator.Construction.standardSymplecticPairing N
      (Local.FunctionsMetaplectic.Construction.symplecticAction g x) (Local.FunctionsMetaplectic.Construction.symplecticAction g y) = _
    simp only [← SchrodingerPairing.Construction.schrodingerPairing_eq_standard]
    exact SchrodingerPairing.Construction.schrodingerPairing_preserved k N g x y⟩

variable (ψ : AddChar k ℂ) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N))

def correctedWeakOpenCell (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
    (f h : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) : ℂ :=
  (Normalization.Construction.openCellScale k N g : ℂ)⁻¹ * UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian ψ
    (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) ν
      (SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg) f h

theorem correctedWeakOpenCell_covariance [ν.IsAddHaarMeasure]
    (hk : ¬ DiscreteTopology k) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (w : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    correctedWeakOpenCell k N ψ ν g hg
      (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu w f).val h.val =
    correctedWeakOpenCell k N ψ ν g hg f.val
      (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu (-Local.FunctionsMetaplectic.Construction.symplecticAction g w) h).val := by
  unfold correctedWeakOpenCell SchrodingerPairing.Construction.schrodingerCayleyPhase
  rw [schrodingerPairing_eq_standardBilinear]
  congr 1
  exact UnitarySplitting.WeakCayleyCoefficients.Construction.weakCayleyGaussian_intertwines hk ψ hc hu ν
    (standardSymplecticOfMatrix k N g) (SchrodingerPairing.Construction.openCellDifference k N g hg)
    (SchrodingerPairing.Construction.openCellDifference_apply k N g hg) f h w

end

/-! Corrected local normalization in the actual Schrödinger convention.

The phase is +β(w,gw)/2 for the Heisenberg cocycle β, and the Weil factor
is γψ(-1)γψ(d). The weak formula specifies every test-function pairing
using the convergent Weyl integral; it introduces no representation,
unitarity, rational-section, or global-compatibility premise. Its actual
unitary realization is proved in UltraWeakUnitary, RealWeakUnitary,
and ComplexWeakUnitary. The historical regularized formula remains
unchanged in Normalization, together with its counterexamples.
-/

open _root_.MeasureTheory
open scoped ComplexConjugate Classical

def correctedWeakOpenCellValue
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (N : ℕ) (ψ : AddChar k ℂ) (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (f h : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) : ℂ :=
  if hg : (g.val - 1).det ≠ 0 then
    correctedWeakOpenCell k N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ)) g hg f h
  else 0

theorem correctedWeakOpenCellValue_open
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (N : ℕ) (ψ : AddChar k ℂ) (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
    (f h : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) :
    correctedWeakOpenCellValue k N ψ g f h =
      correctedWeakOpenCell k N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ)) g hg f h :=
  dite_eq_left hg

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (C : Characters.Construction.GlobalCharacters F d n m)

def correctedFirstFactorScalar (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (u : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) : ℂ :=
  (CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)
      (ArchimedeanAdeles.Construction.rationalScalar F v d))⁻¹ ^ (n * m) *
    ((Normalization.Construction.normCharacterScalar F d v
      ((Normalization.Construction.localDelta F d hd v)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K).val.re : Circle) : ℂ) ^ n *
    (Characters.Construction.localCharacter F d C.χW v
      ((Normalization.Construction.localDelta F d hd v) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) : ℂ)

def correctedSecondFactorScalar (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (u : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) : ℂ :=
  (CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)
      (ArchimedeanAdeles.Construction.rationalScalar F v d))⁻¹ ^ (n * m) *
    ((Normalization.Construction.normCharacterScalar F d v (Matrix.GeneralLinearGroup.det H).val.re : Circle) : ℂ) ^ m *
    (Characters.Construction.localCharacter F d C.χV v
      (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) : ℂ)

/-- The corrected normalizing equations on the two open unitary cells.
All Bruhat test pairings are specified by the explicit local integral. -/
def CorrectedLocalNormalization (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (c : TensorSpace.Construction.SymplecticFrame (ArchimedeanAdeles.Construction.rationalScalar F v d) n m H.val K.val)
    (s : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val →ₜ* Vacuum.Construction.CoverAt F (n * m) C.ψ v) : Prop :=
  (∀ (g : UnitaryBase.Construction.Unitary H.val) (u : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ),
    u.val = g.val.val - 1 → ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (n * m),
      (∫ x, (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
          (s (g, 1)) f).val x * conj (h.val x)
        ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)) =
      correctedFirstFactorScalar F d hd n m C v H K u *
        correctedWeakOpenCellValue (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
          (TensorSpace.Construction.dualPairSymplectic H.val K.val c (g, 1)) f.val h.val) ∧
  (∀ (g : UnitaryBase.Construction.Unitary K.val) (u : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ),
    u.val = g.val.val - 1 → ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (n * m),
      (∫ x, (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
          (s (1, g)) f).val x * conj (h.val x)
        ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)) =
      correctedSecondFactorScalar F d n m C v H K u *
        correctedWeakOpenCellValue (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
          (TensorSpace.Construction.dualPairSymplectic H.val K.val c (1, g)) f.val h.val)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction
