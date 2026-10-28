import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondElimination
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.RangeModulo

/-! # Total Second Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondFiniteness

noncomputable section

/-! Finiteness on the second cohomology page implies finiteness of the original total cohomology. -/

open _root_.CategoryTheory Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiltration OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondClasses

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]

theorem image_step (n q p : ℕ) (hdeg : q + p = n)
    [Module.Finite R ((TotalSecondClasses.horizontal K p).homology q)] [Module.Finite R (TotalFiltration.image K n (q + 1))] :
    Module.Finite R (TotalFiltration.image K n q) :=
  IntegralComparison.Finite.RangeModulo.finite_range (TotalFiltration.classMap K n q) (TotalSecondClasses.secondClassMap K n q p hdeg)
    (TotalFiltration.image K n (q + 1)) (fun x hx => TotalSecondElimination.zero_class_lifts K n q p hdeg x hx)

theorem image_finite (n : ℕ)
    (hrows : ∀ q p, q + p = n → Module.Finite R ((TotalSecondClasses.horizontal K p).homology q))
    (q : ℕ) (hq : q ≤ n + 1) : Module.Finite R (TotalFiltration.image K n q) := by
  induction hq using Nat.decreasingInduction with
  | self =>
      rw [TotalFiltration.image_last]
      infer_instance
  | of_succ q hq ih =>
      let : Module.Finite R (TotalFiltration.image K n (q + 1)) := ih
      have hdeg : q + (n - q) = n := by omega
      let : Module.Finite R ((TotalSecondClasses.horizontal K (n - q)).homology q) := hrows q (n - q) hdeg
      exact image_step K n q (n - q) hdeg

theorem finite (n : ℕ)
    (hrows : ∀ q p, q + p = n → Module.Finite R ((TotalSecondClasses.horizontal K p).homology q)) :
    Module.Finite R ((K.total (.up ℕ)).homology n) := by
  have h := image_finite K n hrows 0 (Nat.zero_le _)
  rw [TotalFiltration.image_zero] at h
  exact ⟨(Submodule.fg_top ⊤).mp h.fg_top⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondFiniteness
