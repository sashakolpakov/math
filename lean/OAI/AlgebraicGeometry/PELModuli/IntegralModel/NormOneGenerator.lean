import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Tactic.LinearCombination

/-! # Norm One Generator -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormOneGenerator

noncomputable section

/-! Primitive norm-one generators reduce CM actions to polarized
similitudes of bounded degree after clearing a fixed denominator. -/

open IntermediateField

variable {E : Type*} [Field E] [Algebra ℚ E]

def conjugateRatio (c : E ≃ₐ[ℚ] E) (a : E) (t : ℚ) : E :=
  (a + algebraMap ℚ E t) / (c a + algebraMap ℚ E t)

theorem nonfixed_add_rat_ne_zero (c : E ≃ₐ[ℚ] E) (a : E) (ha : c a ≠ a) (t : ℚ) :
    a + algebraMap ℚ E t ≠ 0 := by
  intro h
  have he : a = -algebraMap ℚ E t := eq_neg_of_add_eq_zero_left h
  apply ha
  rw [he, map_neg, c.commutes]

theorem conjugate_add_rat_ne_zero (c : E ≃ₐ[ℚ] E) (hc : Function.Involutive c)
    (a : E) (ha : c a ≠ a) (t : ℚ) : c a + algebraMap ℚ E t ≠ 0 := by
  intro h
  have he := congrArg c h
  simp only [map_add, c.commutes, map_zero] at he
  rw [hc a] at he
  exact nonfixed_add_rat_ne_zero c a ha t he

theorem conjugateRatio_injective (c : E ≃ₐ[ℚ] E) (hc : Function.Involutive c)
    (a : E) (ha : c a ≠ a) : Function.Injective (conjugateRatio c a) := by
  intro s t h
  have hd := (div_eq_div_iff (conjugate_add_rat_ne_zero c hc a ha s)
    (conjugate_add_rat_ne_zero c hc a ha t)).mp h
  have he : (c a - a) * (algebraMap ℚ E s - algebraMap ℚ E t) = 0 := by
    linear_combination hd
  have he' := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ha)
  exact (algebraMap ℚ E).injective (sub_eq_zero.mp he')

theorem primitive_norm_one_of_primitive
    [Algebra.IsAlgebraic ℚ E]
    (c : E ≃ₐ[ℚ] E) (hc : Function.Involutive c) (a : E)
    (ha : c a ≠ a) (hprim : IntermediateField.adjoin ℚ {a} = ⊤) :
    ∃ u : E, IntermediateField.adjoin ℚ {u} = ⊤ ∧ u * c u = 1 := by
  have : Finite (IntermediateField ℚ E) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ E ⟨a, hprim⟩
  let u := conjugateRatio c a
  obtain ⟨s, t, hst, hfield⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun t : ℚ => IntermediateField.adjoin ℚ {u t})
  let L := IntermediateField.adjoin ℚ {u s}
  have hus : u s ∈ L := mem_adjoin_simple_self ℚ (u s)
  have hut : u t ∈ L := by
    change u t ∈ IntermediateField.adjoin ℚ {u s}
    rw [hfield]
    exact mem_adjoin_simple_self ℚ (u t)
  have hue : u s - u t ≠ 0 := sub_ne_zero.mpr (fun h => hst (conjugateRatio_injective c hc a ha h))
  have hs : u s * (c a + algebraMap ℚ E s) = a + algebraMap ℚ E s :=
    div_mul_cancel₀ _ (conjugate_add_rat_ne_zero c hc a ha s)
  have ht : u t * (c a + algebraMap ℚ E t) = a + algebraMap ℚ E t :=
    div_mul_cancel₀ _ (conjugate_add_rat_ne_zero c hc a ha t)
  have hrecover : c a =
      ((algebraMap ℚ E s - algebraMap ℚ E t) -
        (u s * algebraMap ℚ E s - u t * algebraMap ℚ E t)) / (u s - u t) := by
    apply (eq_div_iff hue).mpr
    linear_combination hs - ht
  have hca : c a ∈ L := by
    rw [hrecover]
    exact L.div_mem (L.sub_mem (L.sub_mem (L.algebraMap_mem s) (L.algebraMap_mem t))
      (L.sub_mem (L.mul_mem hus (L.algebraMap_mem s)) (L.mul_mem hut (L.algebraMap_mem t))))
        (L.sub_mem hus hut)
  have haL : a ∈ L := by
    have he : a = u s * (c a + algebraMap ℚ E s) - algebraMap ℚ E s := by
      linear_combination -hs
    rw [he]
    exact L.sub_mem (L.mul_mem hus (L.add_mem hca (L.algebraMap_mem s))) (L.algebraMap_mem s)
  have hL : L = ⊤ := top_unique (hprim ▸ (adjoin_simple_le_iff.mpr haL))
  refine ⟨u s, hL, ?_⟩
  change (a + algebraMap ℚ E s) / (c a + algebraMap ℚ E s) *
    c ((a + algebraMap ℚ E s) / (c a + algebraMap ℚ E s)) = 1
  rw [map_div₀, map_add, map_add, c.commutes, hc]
  field_simp [nonfixed_add_rat_ne_zero c a ha s, conjugate_add_rat_ne_zero c hc a ha s]
  exact div_self (mul_ne_zero (nonfixed_add_rat_ne_zero c a ha s)
    (conjugate_add_rat_ne_zero c hc a ha s))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormOneGenerator
