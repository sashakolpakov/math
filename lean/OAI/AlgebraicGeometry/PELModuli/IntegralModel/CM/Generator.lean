import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.NormOneGenerator
import OAI.ArithmeticGeometry.Models.Algebra

/-! # Generator -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.Generator

noncomputable section

/-! A constructed integral primitive CM generator has a fixed rational
conjugate norm. Its action is therefore a candidate polarized similitude
with a fixed multiplier. -/

open IntermediateField

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem cm_integral_primitive_similitude_generator :
    ∃ (d : ℕ) (v : NumberField.RingOfIntegers E), d ≠ 0 ∧
      IntermediateField.adjoin ℚ {(v : E)} = ⊤ ∧
      v * NumberField.IsCMField.ringOfIntegersComplexConj E v = (d : NumberField.RingOfIntegers E) ^ 2 := by
  obtain ⟨u, hu, hnorm⟩ := NormOneGenerator.cm_primitive_norm_one_exists (E := E)
  obtain ⟨d, hd, _, hden⟩ := ArithmeticGeometry.Models.Algebra.Constructions.Foundations.exists_common_natural_denominator E
    (fun _ : Unit => u) 1 one_ne_zero
  obtain ⟨v, hv⟩ := hden Unit.unit
  have hv' : (v : E) = (d : E) * u := hv
  let L := IntermediateField.adjoin ℚ {(v : E)}
  have huL : u ∈ L := by
    have he : u = (v : E) / (d : E) := by
      apply (eq_div_iff (Nat.cast_ne_zero.mpr hd)).mpr
      exact (mul_comm u (d : E)).trans hv'.symm
    rw [he]
    exact L.div_mem (mem_adjoin_simple_self ℚ (v : E)) (L.natCast_mem d)
  have hL : L = ⊤ := top_unique (hu ▸ (adjoin_simple_le_iff.mpr huL))
  refine ⟨d, v, hd, hL, ?_⟩
  apply Subtype.val_injective
  change (v : E) * NumberField.IsCMField.complexConj E (v : E) = (d : E) ^ 2
  rw [hv', map_mul, map_natCast]
  calc
    (d : E) * u * ((d : E) * NumberField.IsCMField.complexConj E u) =
        (d : E) ^ 2 * (u * NumberField.IsCMField.complexConj E u) := by ring
    _ = (d : E) ^ 2 := by rw [hnorm, mul_one]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.Generator
