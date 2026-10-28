import OAI.RepresentationTheory.Weil.AdelicSplitting.SchrodingerPairing

/-! # Corrected Generator Kernels -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction

noncomputable section

section

/-! Corrected open-cell integral in the actual Schrödinger convention.
The historical phasePair, dampedIntertwiner, and openCellOperator are left
unchanged so that their checked counterexample remains valid. -/

open _root_.MeasureTheory Filter
open scoped Classical _root_.Topology

variable (k : Type) [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] (N : ℕ) (ψ : AddChar k ℂ)

def correctedOpenCellKernel (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (w : Local.FunctionsMetaplectic.Construction.PhaseSpace k N)
    (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k N) : ℂ :=
  ψ (SchrodingerPairing.Construction.schrodingerPairing k N w (Local.FunctionsMetaplectic.Construction.symplecticAction g w) / 2) *
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (w - Local.FunctionsMetaplectic.Construction.symplecticAction g w) f x

def correctedDampedIntertwiner (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (ε : ℝ)
    (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k N) : ℂ :=
  (Normalization.Construction.openCellScale k N g : ℂ) *
    ∫ w : Local.FunctionsMetaplectic.Construction.PhaseSpace k N,
      Complex.exp (-((ε * ∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ)) *
        correctedOpenCellKernel k N ψ g w f x
      ∂(Measure.pi (fun _ => Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ))

def correctedOpenCellOperator (g : Local.FunctionsMetaplectic.Construction.Symplectic k N)
    (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k N) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => correctedDampedIntertwiner k N ψ g ε f x)

theorem correctedOpenCellKernel_phase (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (w : Local.FunctionsMetaplectic.Construction.PhaseSpace k N)
    (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k N) :
    correctedOpenCellKernel k N ψ g w f x =
      ψ (-(Normalization.Construction.phasePair k N w (Local.FunctionsMetaplectic.Construction.symplecticAction g w) / 2)) *
        Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (w - Local.FunctionsMetaplectic.Construction.symplecticAction g w) f x := by
  rw [correctedOpenCellKernel, SchrodingerPairing.Construction.schrodingerPairing_eq_neg_phasePair, neg_div]

/-- The existing tensor coordinates identify the Schrödinger cocycle with
the negative trace pairing. Its norm-form Weil constant consequently uses
the negative additive character. -/
def schrodingerQuadraticWeilConstant (d : k) : ℂ :=
  Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-1) * Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ d

end

/-! Independent dilation and Fourier checks for the corrected phase.
The dilation identity holds for every nonzero scalar, and both identities
hold for arbitrary functions and every point over any characteristic-zero
normed field. They precede any evaluation of a Gaussian test integral. -/

open scoped Classical

variable (k : Type) [NormedField k] [CharZero k]

def oneCoordinatePhase (q p : k) : Local.FunctionsMetaplectic.Construction.PhaseSpace k 1 :=
  Sum.elim (fun _ => q) (fun _ => p)

def oneCoordinateDilation (a : k) (ha : a ≠ 0) : Local.FunctionsMetaplectic.Construction.GeneralLinear k 1 where
  val := fun _ _ => a
  inv := fun _ _ => a⁻¹
  val_inv := by
    ext i j
    fin_cases i
    fin_cases j
    change (∑ _ : Fin 1, a * a⁻¹) = 1
    simpa only [Fin.sum_univ_one] using mul_inv_cancel₀ ha
  inv_val := by
    ext i j
    fin_cases i
    fin_cases j
    change (∑ _ : Fin 1, a⁻¹ * a) = 1
    simpa only [Fin.sum_univ_one] using inv_mul_cancel₀ ha

omit [CharZero k] in
theorem schrodingerPairing_oneCoordinates (q p q' p' : k) :
    SchrodingerPairing.Construction.schrodingerPairing k 1 (oneCoordinatePhase k q p) (oneCoordinatePhase k q' p') =
      p * q' - q * p' := by
  rw [SchrodingerPairing.Construction.schrodingerPairing_eq_standard]
  simp [UnitarySplitting.Oscillator.Construction.standardSymplecticPairing, oneCoordinatePhase]

omit [CharZero k] in
theorem oneCoordinateDilation_action (a : k) (ha : a ≠ 0) (q p : k) :
    Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.leviSymplectic (oneCoordinateDilation k a ha)) (oneCoordinatePhase k q p) =
      oneCoordinatePhase k (a * q) (a⁻¹ * p) := by
  funext i
  cases i <;> rename_i i <;> fin_cases i <;>
    simp only [Local.FunctionsMetaplectic.Construction.symplecticAction, Local.Generators.Construction.leviSymplectic, oneCoordinatePhase,
      Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Fin.sum_univ_one]
  · change a * q + 0 * p = a * q
    ring
  · change 0 * q + a⁻¹ * p = a⁻¹ * p
    ring

omit [CharZero k] in
theorem oneCoordinateFourier_action (q p : k) :
    Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k 1) (oneCoordinatePhase k q p) =
      oneCoordinatePhase k p (-q) := by
  funext i
  cases i <;> rename_i i <;> fin_cases i <;>
    simp [Local.FunctionsMetaplectic.Construction.symplecticAction, Local.Generators.Construction.weylSymplectic, oneCoordinatePhase,
      Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

variable (ψ : AddChar k ℂ)

theorem correctedOpenCellKernel_dilation (a : k) (ha : a ≠ 0)
    (f : Local.FunctionsMetaplectic.Construction.Position k 1 → ℂ) (q p x : k) :
    correctedOpenCellKernel k 1 ψ (Local.Generators.Construction.leviSymplectic (oneCoordinateDilation k a ha))
      (oneCoordinatePhase k q p) f (fun _ => x) =
      ψ ((1 - a⁻¹) * p * (x + a * q)) * f (fun _ => x + (a - 1) * q) := by
  rw [correctedOpenCellKernel, oneCoordinateDilation_action, schrodingerPairing_oneCoordinates]
  simp only [Local.FunctionsMetaplectic.Construction.heisenbergFunction, oneCoordinatePhase, Pi.sub_apply, Sum.elim_inr,
    Sum.elim_inl, Fin.sum_univ_one]
  rw [← mul_assoc, ← ψ.map_add_eq_mul]
  congr 2
  · field_simp
    ring
  · funext i
    ring

theorem correctedOpenCellKernel_fourier (f : Local.FunctionsMetaplectic.Construction.Position k 1 → ℂ) (q p x : k) :
    correctedOpenCellKernel k 1 ψ (Local.Generators.Construction.weylSymplectic k 1)
      (oneCoordinatePhase k q p) f (fun _ => x) =
      ψ (p ^ 2 + (p + q) * x) * f (fun _ => x - q + p) := by
  rw [correctedOpenCellKernel, oneCoordinateFourier_action, schrodingerPairing_oneCoordinates]
  simp only [Local.FunctionsMetaplectic.Construction.heisenbergFunction, oneCoordinatePhase, Pi.sub_apply, Sum.elim_inr,
    Sum.elim_inl, Fin.sum_univ_one]
  rw [← mul_assoc, ← ψ.map_add_eq_mul]
  congr 2
  · ring
  · funext i
    ring

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction
