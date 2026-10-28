import OAI.Analysis.PDE.Weak.Elliptic.InteriorEstimate
import OAI.Analysis.PDE.Weak.Boundary.H1Translation

/-! The actual difference-quotient energy estimate through a flat
zero-Dirichlet boundary, in every tangential coordinate direction. -/

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem halfspace_tangential_difference_energy
    (ℓ : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : Continuous A) {lam Λ D K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD0 : 0 ≤ D) (hK0 : 0 ≤ K)
    (hAM : ∀ x, ‖A x‖ ≤ Λ)
    (hell : ∀ x z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero {x | 0 < ℓ x})
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hweak : WeakDivergenceEquation {x | 0 < ℓ x}
      (fieldMultiplierCLM A hA.aestronglyMeasurable (Eventually.of_forall hAM) p.2) f)
    (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηM : ∀ x, |η x| ≤ 1) (hηK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (j : Fin (m + 1)) (htangent : ℓ (Pi.single j 1) = 0) {h : ℝ} (hh : h ≠ 0)
    (hDA : ∀ x, ‖differenceQuotient (Pi.single j 1) h A x‖ ≤ D) :
    ‖cutoffL2 η hη.continuous hηM
      (differenceQuotientL2 volume (Pi.single j 1) h p.2)‖ ^ 2 ≤
      ((‖f‖ + D * ‖p.2‖ + 2 * Λ * (K * ‖p.2‖)) ^ 2 / lam +
        4 * (‖f‖ + D * ‖p.2‖) * (K * ‖p.2‖)) / lam := by
  have hpall : p ∈ H1Zero univ := by
    apply closure_mono (s := smoothH1Graph {x | 0 < ℓ x}) (t := smoothH1Graph univ) _ hp
    rintro q ⟨u, hu, hs, hsu, hq⟩
    exact ⟨u, hu, hs, subset_univ _, hq⟩
  apply interior_difference_energy_of_admissible A hA hlam hΛ hD0 hK0 hAM hell
    p hpall f hweak η hη hηM hηK j hh hDA (Ωtest := {x | 0 < ℓ x})
  let q := cutoffH1Pair η (hη.of_le (by simp)) hηM hηK
    (cutoffH1Pair η (hη.of_le (by simp)) hηM hηK
      (differenceH1Pair (Pi.single j 1) h p))
  have hd : differenceH1Pair (Pi.single j 1) h p ∈ H1Zero {x | 0 < ℓ x} :=
    OAI.Analysis.PDE.Weak.H1Zero.tangential_difference ℓ hp _ htangent h
  have hcut : ∀ q ∈ H1Zero {x | 0 < ℓ x},
      cutoffH1Pair η (hη.of_le (by simp)) hηM hηK q ∈ H1Zero {x | 0 < ℓ x} := by
    intro q hq
    exact OAI.Analysis.PDE.Weak.H1Zero.cutoff hq η hη hηM hηK inter_subset_right
  have hq : q ∈ H1Zero {x | 0 < ℓ x} := hcut _ (hcut _ hd)
  exact ⟨hq, OAI.Analysis.PDE.Weak.H1Zero.tangential_difference ℓ hq _ htangent (-h)⟩

end OAI.Analysis.PDE.Weak
