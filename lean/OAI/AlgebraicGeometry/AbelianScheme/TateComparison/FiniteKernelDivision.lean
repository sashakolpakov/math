import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor
import Mathlib.GroupTheory.OrderOfElement

/-! # Finite Kernel Division -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision.FiniteKernel

noncomputable section

/-! A surjective homomorphism with finite kernel has an additive inverse
up to the kernel cardinality. The map is constructed from its actual fibers. -/

universe u

variable {H H' : Type u} [AddCommGroup H] [AddCommGroup H']
  (f : H →+ H')

theorem card_smul_eq_of_map_eq {x y : H} (h : f x = f y) :
    Nat.card f.ker • x = Nat.card f.ker • y := by
  have hz : x - y ∈ f.ker := by
    change f (x - y) = 0
    rw [map_sub, h, sub_self]
  have he : Nat.card f.ker • (x - y) = 0 :=
    congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨x - y, hz⟩ : f.ker)))
  rwa [nsmul_sub, sub_eq_zero] at he

def inverseMultiple (hf : Function.Surjective f) : H' →+ H where
  toFun y := Nat.card f.ker • (hf y).choose
  map_zero' := by
    exact (card_smul_eq_of_map_eq f ((hf 0).choose_spec.trans f.map_zero.symm)).trans
      (nsmul_zero _)
  map_add' x y := by
    have he : f (hf (x + y)).choose = f ((hf x).choose + (hf y).choose) := by
      rw [(hf (x + y)).choose_spec, map_add, (hf x).choose_spec, (hf y).choose_spec]
    exact (card_smul_eq_of_map_eq f he).trans (nsmul_add _ _ _)

theorem inverseMultiple_comp (hf : Function.Surjective f) :
    (inverseMultiple f hf).comp f = Nat.card f.ker • AddMonoidHom.id H := by
  ext x
  exact card_smul_eq_of_map_eq f (hf (f x)).choose_spec

theorem comp_inverseMultiple (hf : Function.Surjective f) :
    f.comp (inverseMultiple f hf) = Nat.card f.ker • AddMonoidHom.id H' := by
  ext y
  exact (f.map_nsmul _ _).trans (congrArg (fun z => Nat.card f.ker • z) (hf y).choose_spec)

theorem card_ne_zero [Finite f.ker] : Nat.card f.ker ≠ 0 :=
  Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision.FiniteKernel
