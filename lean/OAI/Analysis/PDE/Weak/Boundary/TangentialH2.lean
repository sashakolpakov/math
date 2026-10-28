import OAI.Analysis.PDE.Weak.Boundary.TangentialEnergy
import OAI.Analysis.PDE.Weak.Elliptic.InteriorGeometry
import OAI.Analysis.PDE.Weak.Elliptic.Localization
import Mathlib.Analysis.Normed.Operator.CompleteCodomain

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Genuine boundary H² regularity in tangential directions. The compact
cutoff may cross the flat Dirichlet boundary. -/
theorem halfspace_tangential_weak_gradient_derivative
    (ℓ : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ 1 A) {lam Λ D K L : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hAM : ∀ x, ‖A x‖ ≤ Λ) (hDA : ∀ x, ‖fderiv ℝ A x‖ ≤ D)
    (hell : ∀ x z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero {x | 0 < ℓ x})
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hweak : WeakDivergenceEquation {x | 0 < ℓ x}
      (fieldMultiplierCLM A hA.continuous.aestronglyMeasurable (Eventually.of_forall hAM) p.2) f)
    (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η)
    (hηM : ∀ x, |η x| ≤ 1) (hηK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (hηL : ∀ x, ‖fderiv ℝ η x‖ ≤ L)
    (j : Fin (m + 1)) (htangent : ℓ (Pi.single j 1) = 0) :
    ∃ g : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
      ‖g‖ ≤ Real.sqrt
        (((‖f‖ + D * ‖p.2‖ + 2 * Λ * (K * ‖p.2‖)) ^ 2 / lam +
          4 * (‖f‖ + D * ‖p.2‖) * (K * ‖p.2‖)) / lam) + L * ‖p.2‖ ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffL2 η hη.continuous hηM p.2) g := by
  let : CompleteSpace (OAI.Analysis.PDE.Variational.CellVectors m) := FiniteDimensional.complete ℝ (OAI.Analysis.PDE.Variational.CellVectors m)
  let : CompleteSpace (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) :=
    FiniteDimensional.complete ℝ (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
  let v : OAI.Analysis.PDE.Variational.CellCoordinates m := Pi.single j 1
  have hv : ‖v‖ = 1 := by simp [v, Pi.norm_single]
  obtain ⟨s, hs0, hsn, _⟩ :=
    exists_small_backward_shifts hs.isCompact isOpen_univ (subset_univ _) v hv.le
  let E := ((‖f‖ + D * ‖p.2‖ + 2 * Λ * (K * ‖p.2‖)) ^ 2 / lam +
    4 * (‖f‖ + D * ‖p.2‖) * (K * ‖p.2‖)) / lam
  have hE : 0 ≤ E := by dsimp [E]; positivity
  apply exists_weakDerivative_of_differenceQuotient_bound volume
    (cutoffL2 η hη.continuous hηM p.2)
    (integrable_cutoffL2 volume η hη.continuous hs hηM p.2) v hs0 hsn
  intro n
  have hAD : ∀ x, ‖differenceQuotient v (s n) A x‖ ≤ D := by
    intro x
    simpa only [hv, mul_one] using norm_differenceQuotient_le A hA v x (hsn n)
      (fun t _ ↦ hDA _)
  have hηD : ∀ x, |differenceQuotient v (s n) η x| ≤ L := by
    intro x
    simpa only [hv, mul_one, Real.norm_eq_abs] using
      norm_differenceQuotient_le η (hη.of_le (by simp)) v x (hsn n) (fun t _ ↦ hηL _)
  have henergy := halfspace_tangential_difference_energy ℓ A hA.continuous hlam hΛ hD hK hAM hell
    p hp f hweak η hη hηM hηK j htangent (hsn n) hAD
  have hn : ‖cutoffL2 η hη.continuous hηM
      (differenceQuotientL2 volume v (s n) p.2)‖ ≤ Real.sqrt E := by
    change ‖cutoffL2 η hη.continuous hηM
      (differenceQuotientL2 volume v (s n) p.2)‖ ^ 2 ≤ E at henergy
    nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg E,
      norm_nonneg (cutoffL2 η hη.continuous hηM (differenceQuotientL2 volume v (s n) p.2))]
  exact (norm_differenceQuotientL2_cutoff_le volume η hη.continuous hηM v (s n) hηD p.2).trans
    (add_le_add hn le_rfl)

end OAI.Analysis.PDE.Weak
