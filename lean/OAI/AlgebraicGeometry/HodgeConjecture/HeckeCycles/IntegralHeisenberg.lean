import OAI.RepresentationTheory.Weil.Local.NonarchimedeanFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.Heisenberg

/-! # Integral Heisenberg -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralHeisenberg.CM

noncomputable section

/-! Integral phase translations fix the lattice vacuum when the
character is trivial on the integers and one half is integral. -/

open scoped Classical
open OAI.RepresentationTheory.Weil.Local.NonarchimedeanFourier.Construction OAI.RepresentationTheory.Weil.UnitarySplitting.Heisenberg.Construction

variable {k : Type} [NormedField k] {N : ℕ}

def indicator (O : Subring k) (x : Fin N → k) : ℂ := if ∀ i, x i ∈ O then 1 else 0

theorem shifted_mem (O : Subring k) (q x : Fin N → k) (hq : ∀ i, q i ∈ O) :
    (∀ i, x i - q i ∈ O) ↔ ∀ i, x i ∈ O := by
  constructor
  · intro h i
    simpa only [sub_add_cancel] using O.add_mem (h i) (hq i)
  · intro h i
    exact O.sub_mem (h i) (hq i)

theorem fixed (O : Subring k) (ψ : AddChar k ℂ)
    (hψ : ∀ x ∈ O, ψ x = 1) (hh : (2 : k)⁻¹ ∈ O)
    (v : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) (hv : ∀ i, v i ∈ O) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v (indicator O) = indicator O := by
  funext x
  have hs := shifted_mem O (fun i => v (.inl i)) x (fun i => hv (.inl i))
  change ψ (∑ i, v (.inr i) * (x i - v (.inl i) / 2)) *
    (if ∀ i, x i - v (.inl i) ∈ O then (1 : ℂ) else 0) =
      (if ∀ i, x i ∈ O then (1 : ℂ) else 0)
  rw [if_congr hs rfl rfl]
  by_cases hx : ∀ i, x i ∈ O
  · rw [ite_eq_left hx, mul_one, hψ]
    apply O.sum_mem
    intro i _
    exact O.mul_mem (hv (.inr i)) (O.sub_mem (hx i)
      (by rw [div_eq_mul_inv]; exact O.mul_mem (hv (.inl i)) hh))
  · rw [ite_eq_right hx, mul_zero]

def operator [CharZero k] [NonarchimedeanAddGroup k] (ψ : AddChar k ℂ)
    (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ) (v : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N where
  toFun f := ⟨RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val, RepresentationTheory.Weil.Local.NonarchimedeanFourier.Construction.nonarchimedean_heisenberg_mem ψ hu hc v f⟩
  invFun f := ⟨RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (-v) f.val, RepresentationTheory.Weil.Local.NonarchimedeanFourier.Construction.nonarchimedean_heisenberg_mem ψ hu hc (-v) f⟩
  left_inv f := Subtype.ext (RepresentationTheory.Weil.UnitarySplitting.Heisenberg.Construction.heisenbergFunction_neg_left_cancel ψ v f.val)
  right_inv f := Subtype.ext (RepresentationTheory.Weil.UnitarySplitting.Heisenberg.Construction.heisenbergFunction_neg_right_cancel ψ v f.val)
  map_add' f g := Subtype.ext ((RepresentationTheory.Weil.UnitarySplitting.Heisenberg.Construction.heisenbergLinearEquiv ψ v).map_add f.val g.val)
  map_smul' z f := Subtype.ext (RepresentationTheory.Weil.UnitarySplitting.Oscillator.Construction.heisenbergFunction_smul N ψ v z f.val)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralHeisenberg.CM
