import OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace
import Mathlib.NumberTheory.Padics.ProperSpace

/-! # Local Unit Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalUnitTest

noncomputable section

/-! The q-adic unit-ball test is the unique line fixed by integral
Heisenberg translations and modulations for the conductor-zero character. -/

open scoped Classical
open OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace.Construction

variable (q : ℕ) [Fact q.Prime] (n : ℕ)

def padicUnitIndicator (x : Fin n → ℚ_[q]) : ℂ :=
  if ∀ i, ‖x i‖ ≤ 1 then 1 else 0

theorem padicUnitIndicator_of_integral (x : Fin n → ℚ_[q]) (hx : ∀ i, ‖x i‖ ≤ 1) :
    padicUnitIndicator q n x = 1 := by
  rw [padicUnitIndicator, ite_eq_left hx]

theorem padicUnitIndicator_of_not_integral (x : Fin n → ℚ_[q]) (hx : ¬ ∀ i, ‖x i‖ ≤ 1) :
    padicUnitIndicator q n x = 0 := by
  rw [padicUnitIndicator, ite_eq_right hx]

theorem padicUnitIndicator_closedBall :
    padicUnitIndicator q n =
      (Metric.closedBall (0 : Fin n → ℚ_[q]) 1).indicator (fun _ => (1 : ℂ)) := by
  funext x
  have hm : x ∈ Metric.closedBall (0 : Fin n → ℚ_[q]) 1 ↔ ∀ i, ‖x i‖ ≤ 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  by_cases hx : ∀ i, ‖x i‖ ≤ 1
  · rw [Set.indicator_of_mem (hm.mpr hx)]
    simp only [padicUnitIndicator, ite_eq_left hx]
  · rw [Set.indicator_of_notMem (fun h => hx (hm.mp h))]
    simp only [padicUnitIndicator, ite_eq_right hx]

def padicUnitTest : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n := by
  refine ⟨padicUnitIndicator q n, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem ?_ ?_⟩
  · rw [padicUnitIndicator_closedBall]
    exact (LocallyConstant.charFn ℂ
      (IsUltrametricDist.isClopen_closedBall (0 : Fin n → ℚ_[q]) one_ne_zero)).isLocallyConstant
  · rw [padicUnitIndicator_closedBall]
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℚ_[q]) 1)
    intro x hx
    exact Set.indicator_of_notMem hx _

theorem padicUnitTest_zero : (padicUnitTest q n).val 0 = 1 := by
  simp [padicUnitTest, padicUnitIndicator]

theorem padicUnitIndicator_heisenberg
    (hq : 2 < q) (ψ : AddChar ℚ_[q] ℂ) (hψ : ∀ x, ψ x = 1 ↔ ‖x‖ ≤ 1)
    (v : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] n) (hv : ∀ i, ‖v i‖ ≤ 1) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v (padicUnitIndicator q n) = padicUnitIndicator q n := by
  have htwo : (2 : ℚ_[q])⁻¹ ∈ PadicInt.subring q := by
    have hn : ‖(2 : ℚ_[q])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr
      ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq))
    change ‖(2 : ℚ_[q])⁻¹‖ ≤ 1
    rw [norm_inv, hn, inv_one]
  funext x
  by_cases hx : ∀ i, ‖x i‖ ≤ 1
  · have hs : ∀ i, ‖x i - v (.inl i)‖ ≤ 1 :=
      fun i => (PadicInt.subring q).sub_mem (hx i) (hv (.inl i))
    have hp : ψ (∑ i, v (.inr i) * (x i - v (.inl i) / 2)) = 1 := by
      apply (hψ _).mpr
      apply (PadicInt.subring q).sum_mem
      intro i _
      apply (PadicInt.subring q).mul_mem (hv (.inr i))
      apply (PadicInt.subring q).sub_mem (hx i)
      exact (PadicInt.subring q).mul_mem (hv (.inl i)) htwo
    simp only [RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction, hp, padicUnitIndicator, ite_eq_left hs, ite_eq_left hx, one_mul]
  · have hs : ¬ ∀ i, ‖x i - v (.inl i)‖ ≤ 1 := by
      intro h
      apply hx
      intro i
      have hi := (PadicInt.subring q).add_mem (h i) (hv (.inl i))
      simpa only [sub_add_cancel, PadicInt.mem_subring_iff] using hi
    simp only [RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction, padicUnitIndicator, ite_eq_right hs, ite_eq_right hx, mul_zero]

theorem integral_heisenberg_fixed_scalar
    (ψ : AddChar ℚ_[q] ℂ) (hψ : ∀ x, ψ x = 1 ↔ ‖x‖ ≤ 1)
    (f : (Fin n → ℚ_[q]) → ℂ)
    (hf : ∀ v : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] n, (∀ i, ‖v i‖ ≤ 1) → RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f = f) :
    ∀ x, f x = f 0 * padicUnitIndicator q n x := by
  intro x
  have hψ0 : ψ (0 : ℚ_[q]) = 1 := (hψ 0).mpr (by simp)
  by_cases hx : ∀ i, ‖x i‖ ≤ 1
  · have hv : ∀ i, ‖(Sum.elim x 0 : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] n) i‖ ≤ 1 := by
      intro i
      cases i with
      | inl i => exact hx i
      | inr i => simp
    have h := congrFun (hf (Sum.elim x 0) hv) x
    simp only [RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction, Sum.elim_inr, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, hψ0, Sum.elim_inl, sub_self, one_mul] at h
    change f 0 = f x at h
    rw [padicUnitIndicator, ite_eq_left hx, mul_one]
    exact h.symm
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hv : ∀ j, ‖(Sum.elim 0 (Pi.single i 1) : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] n) j‖ ≤ 1 := by
      intro j
      cases j with
      | inl j => simp
      | inr j => simp only [Sum.elim_inr, Pi.single_apply]; split_ifs <;> simp
    have h := congrFun (hf (Sum.elim 0 (Pi.single i 1)) hv) x
    have hp : ψ (x i) ≠ 1 := fun h => hi ((hψ _).mp h)
    have hm : ψ (x i) * f x = f x := by
      simpa [RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction, Pi.single_apply] using h
    have hz : (ψ (x i) - 1) * f x = 0 := by
      rw [sub_mul, one_mul, hm, sub_self]
    have hf0 : f x = 0 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hp)
    simp only [hf0, padicUnitIndicator, ite_eq_right hx, mul_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalUnitTest
