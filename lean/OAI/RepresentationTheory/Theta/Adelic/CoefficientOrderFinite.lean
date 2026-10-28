import OAI.RepresentationTheory.Theta.Adelic.PrincipalCoefficientOrder

/-! # Coefficient Order Finite -/

namespace OAI.RepresentationTheory.Theta.Adelic.CoefficientOrderFinite

noncomputable section

/-! The actual coefficient order is a finitely generated, torsion-free
integer module, so integral lattice congruence arguments apply to it. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.PrincipalCoefficientOrder

variable (F : Type) [Field F] [NumberField F] (d : F)
variable (N : ℕ) (q : 𝓞 F) (hq : (q : F) = (N : F) * d)

def coefficientLinear : (𝓞 F × 𝓞 F) →ₗ[ℤ] PrincipalCoefficientOrder.coefficientOrder F d N q hq where
  toFun a := ⟨⟨(a.1 : F), (N : F) * (a.2 : F)⟩, a.1, a.2, rfl⟩
  map_add' a b := by
    apply Subtype.ext
    ext <;> simp [mul_add]
  map_smul' n a := by
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · simp
    · simp [mul_left_comm]

omit [NumberField F] in
theorem coefficientLinear_surjective : Function.Surjective (coefficientLinear F d N q hq) := by
  intro x
  obtain ⟨a, b, h⟩ := x.property
  exact ⟨(a, b), Subtype.ext h.symm⟩

theorem coefficientOrder_finite : Module.Finite ℤ (PrincipalCoefficientOrder.coefficientOrder F d N q hq) :=
  Module.Finite.of_surjective (coefficientLinear F d N q hq) (coefficientLinear_surjective F d N q hq)

theorem coefficientOrder_torsionFree : Module.IsTorsionFree ℤ (PrincipalCoefficientOrder.coefficientOrder F d N q hq) := by
  apply Function.Injective.moduleIsTorsionFree
    (fun x : PrincipalCoefficientOrder.coefficientOrder F d N q hq => (x.val.re, x.val.im))
  · intro x y h
    apply Subtype.ext
    exact QuadraticAlgebra.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  · intro n x
    ext <;> simp

end

end OAI.RepresentationTheory.Theta.Adelic.CoefficientOrderFinite
