import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormOneGenerator

/-! # Norm One Generator -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.NormOneGenerator

noncomputable section

/-! Construct a primitive element of a CM field with norm one under
its actual complex conjugation. -/

open IntermediateField

variable {E : Type*} [Field E] [Algebra ℚ E]

theorem primitive_not_fixed (c : E ≃ₐ[ℚ] E) (hc : c ≠ 1)
    (a : E) (ha : IntermediateField.adjoin ℚ {a} = ⊤) : c a ≠ a := by
  intro h
  apply hc
  apply AlgEquiv.ext
  intro x
  change c x = x
  have hx : x ∈ IntermediateField.adjoin ℚ {a} := by rw [ha]; trivial
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact h
  | algebraMap y => exact c.commutes y
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem cm_primitive_norm_one_exists [NumberField E] [NumberField.IsCMField E] :
    ∃ u : E, IntermediateField.adjoin ℚ {u} = ⊤ ∧
      u * NumberField.IsCMField.complexConj E u = 1 := by
  let c : E ≃ₐ[ℚ] E := (NumberField.IsCMField.complexConj E).restrictScalars ℚ
  have hc : Function.Involutive c := NumberField.IsCMField.complexConj_apply_apply E
  have hn : c ≠ 1 := by
    intro h
    apply NumberField.IsCMField.complexConj_ne_one E
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun g : E ≃ₐ[ℚ] E => g x) h
  obtain ⟨a, ha⟩ := Field.exists_primitive_element ℚ E
  exact NormOneGenerator.primitive_norm_one_of_primitive c hc a (primitive_not_fixed c hn a ha) ha

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.NormOneGenerator
