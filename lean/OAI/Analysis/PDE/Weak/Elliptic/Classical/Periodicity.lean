import OAI.Analysis.PDE.Weak.Elliptic.PeriodicClassical

noncomputable section
open Set _root_.MeasureTheory Filter
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem coordinatePeriodShift_mem_of_backward_invariant
    (J : Finset (Fin (m + 1))) (L : OAI.Analysis.PDE.Variational.CellCoordinates m)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (hΩ : ∀ z x, x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J L z ∈ Ω → x ∈ Ω) :
    ∀ z x, x ∈ Ω → x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J L z ∈ Ω := by
  intro z x hx
  apply hΩ (-z) (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J L z)
  simpa only [map_neg, add_neg_cancel_right] using hx

theorem continuous_representative_translation
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    {u w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hu : ContinuousOn u Ω)
    (heq : ∀ᵐ x ∂volume, x ∈ Ω → u x = w x)
    (c : OAI.Analysis.PDE.Variational.CellCoordinates m) (hc : ∀ x ∈ Ω, x + c ∈ Ω)
    (hw : ∀ x, w (x + c) = w x) : ∀ x ∈ Ω, u (x + c) = u x := by
  have hu' : ContinuousOn (fun x ↦ u (x + c)) Ω :=
    hu.comp (continuous_id.add_const c).continuousOn hc
  apply continuous_eqOn_of_local_ae hΩ hu' hu
  have heq' := (measurePreserving_add_right (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) c).quasiMeasurePreserving.ae heq
  filter_upwards [heq, heq'] with x hx hy
  intro hxs
  rw [hy (hc x hxs), hx hxs, hw x]

theorem continuous_periodic_value_representative
    (J : Finset (Fin (m + 1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) (hL : ∀ i ∈ J, a i < b i)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hshift : ∀ z x, x ∈ Ω → x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b - a) z ∈ Ω)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hu : ContinuousOn u Ω)
    (heq : ∀ᵐ x ∂volume, x ∈ Ω → u x = OAI.Analysis.PDE.Variational.periodicRepresentative J a b f x) :
    ∀ (z : J → ℤ) x, x ∈ Ω → u (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b - a) z) = u x := by
  intro z
  exact continuous_representative_translation hΩ hu heq _ (hshift z)
    (OAI.Analysis.PDE.Variational.periodicRepresentative_periodic J a b hL f z)

/-- The classical representative of the actual periodic variational solution is
exactly periodic, not merely periodic almost everywhere. -/
theorem periodic_weak_solution_smooth_periodic
    (J : Finset (Fin (m + 1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) (hab : a ≤ b)
    (hL : ∀ i ∈ J, a i < b i) (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (hopen : IsOpen Ω)
    (htrans : Ω ⊆ OAI.Analysis.PDE.Variational.transverseInterior J a b)
    (hΩ : ∀ z x, x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b - a) z ∈ Ω → x ∈ Ω)
    (k : Fin (m + 1)) (hk : k ∉ J)
    (hface : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (u : OAI.Analysis.PDE.Variational.PeriodicH10 a b Ω (OAI.Analysis.PDE.Variational.coordinatePeriodSet J (b - a)))
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (hA : ContDiff ℝ ∞ A)
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (hweak : WeakDivergenceEquation Ω
      (fun y ↦ A y (OAI.Analysis.PDE.Variational.periodicRepresentative J a b u.val y)) (OAI.Analysis.PDE.Variational.periodicRepresentative J a b f))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ y ∂volume, y ∈ Ω → OAI.Analysis.PDE.Variational.periodicRepresentative J a b f y = g y) :
    ∃ v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiffOn ℝ ∞ v Ω ∧
      (∀ᵐ y ∂volume, y ∈ Ω → v y = OAI.Analysis.PDE.Variational.periodicRepresentative J a b (OAI.Analysis.PDE.Variational.periodicValue a b Ω _ u) y) ∧
      (∀ x ∈ Ω, -classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient v y)) x = g x) ∧
      (∀ (z : J → ℤ) x, x ∈ Ω → v (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b - a) z) = v x) := by
  obtain ⟨v, hv, heq, hpde⟩ := periodic_weak_solution_classical_representative
    J a b hab hL Ω hopen htrans hΩ k hk hface u A hA hlam hell f hweak g hg hfg
  refine ⟨v, hv, heq, hpde, ?_⟩
  exact continuous_periodic_value_representative J a b hL hopen
    (coordinatePeriodShift_mem_of_backward_invariant J (b - a) hΩ)
    (OAI.Analysis.PDE.Variational.periodicValue a b Ω _ u) v hv.continuousOn heq

end OAI.Analysis.PDE.Weak
