import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicIdentity
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Topology.Germ
import Mathlib.RingTheory.LocalRing.Defs

/-! # Holomorphic Germs -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs

noncomputable section

/-!
# The domain of holomorphic germs

Holomorphic germs are function germs represented by a complex differentiable
function on an open neighborhood. The identity principle makes this ring an
integral domain, allowing fraction-field algebra on local coefficients.
-/

open Set Filter
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def holomorphicGerms (x : E) : Subring (Germ (𝓝 x) ℂ) where
  carrier a := ∃ (f : E → ℂ), (f : Germ (𝓝 x) ℂ) = a ∧
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ DifferentiableOn ℂ f U
  zero_mem' := ⟨0, rfl, univ, isOpen_univ, mem_univ _, differentiableOn_const _⟩
  one_mem' := ⟨1, rfl, univ, isOpen_univ, mem_univ _, differentiableOn_const _⟩
  add_mem' := by
    rintro a b ⟨f, rfl, U, hU, hxU, hf⟩ ⟨g, rfl, V, hV, hxV, hg⟩
    exact ⟨f + g, Germ.coe_add _ _, U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
      (hf.mono inter_subset_left).add (hg.mono inter_subset_right)⟩
  mul_mem' := by
    rintro a b ⟨f, rfl, U, hU, hxU, hf⟩ ⟨g, rfl, V, hV, hxV, hg⟩
    exact ⟨f * g, Germ.coe_mul _ _, U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
      (hf.mono inter_subset_left).mul (hg.mono inter_subset_right)⟩
  neg_mem' := by
    rintro a ⟨f, rfl, U, hU, hxU, hf⟩
    exact ⟨-f, Germ.coe_neg _, U, hU, hxU, hf.neg⟩

abbrev HolomorphicGerm (x : E) := ↥(holomorphicGerms x)

instance (x : E) : NoZeroDivisors (HolomorphicGerm x) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    obtain ⟨f, hfa, U, hU, hxU, hf⟩ := a.property
    obtain ⟨g, hgb, V, hV, hxV, hg⟩ := b.property
    have hprod : ∀ᶠ z in 𝓝 x, f z * g z = 0 := by
      apply Germ.coe_eq.mp
      change ((f * g : E → ℂ) : Germ (𝓝 x) ℂ) = 0
      rw [Germ.coe_mul, hfa, hgb]
      exact congrArg Subtype.val hab
    obtain ⟨W, hWprod, hW, hxW⟩ := mem_nhds_iff.mp hprod
    have hfg := HolomorphicIdentity.Constructions.Identity.eventually_zero_or_eventually_zero_of_mul
      ((hU.inter hV).inter hW) ⟨⟨hxU, hxV⟩, hxW⟩
      (hf.mono (fun _ hz => hz.1.1)) (hg.mono (fun _ hz => hz.1.2))
      (fun z hz => hWprod hz.2)
    rcases hfg with hf0 | hg0
    · left
      apply Subtype.ext
      change a.val = 0
      rw [← hfa]
      exact Germ.coe_eq.mpr hf0
    · right
      apply Subtype.ext
      change b.val = 0
      rw [← hgb]
      exact Germ.coe_eq.mpr hg0

instance (x : E) : IsDomain (HolomorphicGerm x) := NoZeroDivisors.to_isDomain _

theorem mul_eq_zero_iff (x : E) (a b : HolomorphicGerm x) :
    a * b = 0 ↔ a = 0 ∨ b = 0 := _root_.mul_eq_zero

def ofFunction (x : E) (f : E → ℂ) {U : Set E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) : HolomorphicGerm x :=
  ⟨f, f, rfl, U, hU, hx, hf⟩

def valueHom (x : E) : HolomorphicGerm x →+* ℂ :=
  Germ.valueRingHom.comp (holomorphicGerms x).subtype

theorem value_ofFunction (x : E) (f : E → ℂ) {U : Set E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) :
    valueHom x (ofFunction x f hU hx hf) = f x := rfl

instance (x : E) : CharZero (HolomorphicGerm x) where
  cast_injective n m h := Nat.cast_injective (R := ℂ) (by simpa only [map_natCast] using congrArg (valueHom x) h)

theorem isUnit_iff_value_ne_zero (x : E) (a : HolomorphicGerm x) :
    IsUnit a ↔ valueHom x a ≠ 0 := by
  constructor
  · intro h
    exact (h.map (valueHom x)).ne_zero
  · intro ha
    obtain ⟨f, hfa, U, hU, hxU, hf⟩ := a.property
    have hvalue : valueHom x a = f x := by
      change Germ.value a.val = f x
      rw [← hfa]
      rfl
    have hfx : f x ≠ 0 := hvalue ▸ ha
    let V := U ∩ f ⁻¹' ({0} : Set ℂ)ᶜ
    have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
    have hxV : x ∈ V := ⟨hxU, hfx⟩
    have hinv : DifferentiableOn ℂ (fun z => (f z)⁻¹) V :=
      (hf.mono inter_subset_left).fun_inv (fun _ hz => hz.2)
    let b := ofFunction x (fun z => (f z)⁻¹) hV hxV hinv
    apply isUnit_iff_exists_inv.mpr
    refine ⟨b, ?_⟩
    apply Subtype.ext
    change a.val * (b : Germ (𝓝 x) ℂ) = 1
    rw [← hfa]
    apply Germ.coe_eq.mpr
    filter_upwards [hV.mem_nhds hxV] with z hz
    exact mul_inv_cancel₀ hz.2

instance (x : E) : IsLocalRing (HolomorphicGerm x) where
  isUnit_or_isUnit_of_add_one := by
    intro a b hab
    by_cases ha : valueHom x a = 0
    · right
      apply (isUnit_iff_value_ne_zero x b).mpr
      have hv := congrArg (valueHom x) hab
      simp only [map_add, map_one, ha, zero_add] at hv
      exact hv ▸ one_ne_zero
    · exact Or.inl ((isUnit_iff_value_ne_zero x a).mpr ha)

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs
