import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.RangeModulo
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiltration

/-! # Total Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiniteness

noncomputable section

/-! Finite row homology implies finite homology of the actual first-quadrant total complex. -/

open _root_.CategoryTheory Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiltration

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  [K.HasTotal (.up ℕ)]

theorem image_step (n q p : ℕ) (hdeg : q + p = n)
    [Module.Finite R ((K.X q).homology p)] [Module.Finite R (TotalFiltration.image K n (q + 1))] :
    Module.Finite R (TotalFiltration.image K n q) :=
  IntegralComparison.Finite.RangeModulo.finite_range (TotalFiltration.classMap K n q) (TotalFiltration.rowClassMap K n q p hdeg)
    (TotalFiltration.image K n (q + 1)) (fun x hx => TotalFiltration.zero_row_class_lifts K n q p hdeg x hx)

theorem image_finite (n : ℕ)
    (hrows : ∀ q p, q + p = n → Module.Finite R ((K.X q).homology p))
    (q : ℕ) (hq : q ≤ n + 1) : Module.Finite R (TotalFiltration.image K n q) := by
  induction hq using Nat.decreasingInduction with
  | self =>
      rw [TotalFiltration.image_last]
      infer_instance
  | of_succ q hq ih =>
      let : Module.Finite R (TotalFiltration.image K n (q + 1)) := ih
      have hdeg : q + (n - q) = n := by omega
      let : Module.Finite R ((K.X q).homology (n - q)) := hrows q (n - q) hdeg
      exact image_step K n q (n - q) hdeg

theorem finite (n : ℕ)
    (hrows : ∀ q p, q + p = n → Module.Finite R ((K.X q).homology p)) :
    Module.Finite R ((K.total (.up ℕ)).homology n) := by
  have h := image_finite K n hrows 0 (Nat.zero_le _)
  rw [TotalFiltration.image_zero] at h
  exact ⟨(Submodule.fg_top ⊤).mp h.fg_top⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiniteness
