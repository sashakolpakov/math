import OAI.Analysis.PDE.Weak.Elliptic.InteriorH2
import OAI.Analysis.PDE.Weak.Elliptic.H1CutoffDerivative
import OAI.Analysis.PDE.Weak.Elliptic.SmoothGradient

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The differentiated local weak solution remains in the actual H¹
completion, not merely in a separately specified weak-derivative space. -/
theorem interior_H1_derivative
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ 1 A) {lam Λ D K L : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hAM : ∀ x, ‖A x‖ ≤ Λ) (hDA : ∀ x, ‖fderiv ℝ A x‖ ≤ D)
    (hell : ∀ x z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hweak : WeakDivergenceEquation Ω
      (fieldMultiplierCLM A hA.continuous.aestronglyMeasurable (Eventually.of_forall hAM) p.2) f)
    (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η)
    (hηM : ∀ x, |η x| ≤ 1) (hηK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (hηL : ∀ x, ‖fderiv ℝ η x‖ ≤ L) (hsub : tsupport η ⊆ Ω)
    (j : Fin (m + 1)) :
    ∃ q : H1Pair m, q ∈ H1Zero univ ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffH1Pair η (hη.of_le (by simp)) hηM hηK p).1 q.1 ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffH1Pair η (hη.of_le (by simp)) hηM hηK p).2 q.2 := by
  let : CompleteSpace (OAI.Analysis.PDE.Variational.CellVectors m) := FiniteDimensional.complete ℝ (OAI.Analysis.PDE.Variational.CellVectors m)
  let : CompleteSpace (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) :=
    FiniteDimensional.complete ℝ (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
  let v : OAI.Analysis.PDE.Variational.CellCoordinates m := Pi.single j 1
  have hv : ‖v‖ = 1 := by simp [v, Pi.norm_single]
  obtain ⟨s, hs0, hsn, hshift⟩ :=
    exists_small_backward_shifts hs.isCompact hΩ hsub v hv.le
  obtain ⟨J, -, hJ⟩ := exists_cellGradient_derivative_bound hη hs
  have hg : ContDiff ℝ 1 (OAI.Analysis.PDE.Variational.cellGradient η) := (contDiff_cellGradient hη).of_le (by simp)
  let E := ((‖f‖ + D * ‖p.2‖ + 2 * Λ * (K * ‖p.2‖)) ^ 2 / lam +
    4 * (‖f‖ + D * ‖p.2‖) * (K * ‖p.2‖)) / lam
  have hE : 0 ≤ E := by dsimp [E]; positivity
  apply exists_H1_derivative_cutoff_of_weighted_difference_bounds p hp η hη hs
    hηM hηK j hs0 hsn (L := L) (J := J) (C := Real.sqrt E)
  · intro n x
    simpa only [hv, mul_one, Real.norm_eq_abs] using
      norm_differenceQuotient_le η (hη.of_le (by simp)) v x (hsn n) (fun t _ ↦ hηL _)
  · intro n x
    simpa only [hv, mul_one] using
      norm_differenceQuotient_le (OAI.Analysis.PDE.Variational.cellGradient η) hg v x (hsn n) (fun t _ ↦ hJ _)
  · intro n
    have hAD : ∀ x, ‖differenceQuotient v (s n) A x‖ ≤ D := by
      intro x
      simpa only [hv, mul_one] using norm_differenceQuotient_le A hA v x (hsn n)
        (fun t _ ↦ hDA _)
    have henergy := interior_difference_energy A hA.continuous hlam hΛ hD hK hAM hell
      p hp f hweak η hη hηM hηK j (hsn n) hAD hsub (hshift n)
    change ‖cutoffL2 η hη.continuous hηM
      (differenceQuotientL2 volume v (s n) p.2)‖ ^ 2 ≤ E at henergy
    nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg E,
      norm_nonneg (cutoffL2 η hη.continuous hηM (differenceQuotientL2 volume v (s n) p.2))]

end OAI.Analysis.PDE.Weak
