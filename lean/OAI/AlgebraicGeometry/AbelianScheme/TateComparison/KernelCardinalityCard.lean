import Mathlib.GroupTheory.Index
import Lean.Util.CollectAxioms

/-! # Kernel Cardinality Card -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelCardinalityCard.KernelCardinality

noncomputable section

/-! Exact kernel cardinalities for a composite of actual surjective
point maps. The identity applies even when the ambient groups are infinite. -/

variable {A B C : Type*} [Group A] [Group B] [Group C]
  (f : A →* B) (g : B →* C)

def projection : (g.comp f).ker →* g.ker where
  toFun x := ⟨f x.val, x.property⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x.val y.val)

theorem projection_surjective (hf : Function.Surjective f) :
    Function.Surjective (projection f g) := by
  intro y
  obtain ⟨x, hx⟩ := hf y.val
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change g (f x) = 1
  rw [hx]
  exact y.property

def kernelEquiv : (projection f g).ker ≃* f.ker where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, by
    change g (f x.val) = 1
    rw [x.property, g.map_one]⟩, Subtype.ext x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem card_comp_kernel (hf : Function.Surjective f) :
    Nat.card (g.comp f).ker = Nat.card f.ker * Nat.card g.ker := by
  have hi : (projection f g).ker.index = Nat.card g.ker :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (projection f g)
      (projection_surjective f g hf)).toEquiv
  calc
    Nat.card (g.comp f).ker = Nat.card (projection f g).ker * (projection f g).ker.index :=
      (projection f g).ker.card_mul_index.symm
    _ = Nat.card f.ker * Nat.card g.ker := by rw [Nat.card_congr (kernelEquiv f g).toEquiv, hi]

theorem finite_second_kernel (hf : Function.Surjective f) [Finite (g.comp f).ker] : Finite g.ker :=
  Finite.of_surjective (projection f g) (projection_surjective f g hf)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelCardinalityCard.KernelCardinality
