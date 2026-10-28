import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.AlgebraCharacter
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.Coalgebra.GroupLike

/-! # Coalgebra Group Like -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.CoalgebraGroupLike

noncomputable section

/-! Finite cocommutative coalgebras over an algebraically closed field have group-like elements. -/

universe u v w

open _root_.Module TensorProduct Coalgebra WithConv

variable (k : Type u) [Field k]
  (C : Type v) [AddCommGroup C] [Module k C] [Module.Finite k C]

/-- Rank-one tensor functionals separate elements of a finite tensor product. -/
theorem tensor_eq_of_duals
    (D : Type w) [AddCommGroup D] [Module k D] [Module.Finite k D]
    {x y : C ⊗[k] D}
    (h : ∀ f : Dual k C, ∀ g : Dual k D,
      dualDistrib k C D (f ⊗ₜ g) x = dualDistrib k C D (f ⊗ₜ g) y) : x = y := by
  apply (Module.evalEquiv k (C ⊗[k] D)).injective
  apply LinearMap.ext
  intro φ
  obtain ⟨z, rfl⟩ := (dualDistribEquiv k C D).surjective φ
  change ((dualDistribEquiv k C D).toLinearMap z) x =
    ((dualDistribEquiv k C D).toLinearMap z) y
  rw [toLinearMap_dualDistribEquiv]
  induction z using TensorProduct.inductionOn with
  | tmul f g => exact h f g
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

omit [Module.Finite k C] in
/-- The tensor-dual evaluation is the scalar multiplication used by convolution. -/
theorem dualDistrib_eq_mul (f g : Dual k C) (z : C ⊗[k] C) :
    dualDistrib k C C (f ⊗ₜ g) z =
      LinearMap.mul' k k (TensorProduct.map f g z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, ha, hb]

variable [Coalgebra k C]

/-- A character of the convolution algebra is represented by an actual coalgebra element. -/
def characterPoint (χ : WithConv (Dual k C) →ₐ[k] k) : C :=
  (Module.evalEquiv k C).symm
    (χ.toLinearMap.comp (WithConv.linearEquiv k (Dual k C)).symm.toLinearMap)

theorem characterPoint_eval (χ : WithConv (Dual k C) →ₐ[k] k) (f : Dual k C) :
    f (characterPoint k C χ) = χ (toConv f) := by
  simp [characterPoint]

/-- Multiplicativity of the algebra character gives the group-like coalgebra identities. -/
theorem characterPoint_groupLike (χ : WithConv (Dual k C) →ₐ[k] k) :
    IsGroupLikeElem k (characterPoint k C χ) := by
  constructor
  · have h := characterPoint_eval k C χ (1 : WithConv (Dual k C)).ofConv
    simpa using h
  · apply tensor_eq_of_duals k C C
    intro f g
    rw [dualDistrib_apply, dualDistrib_eq_mul]
    change (toConv f * toConv g) (characterPoint k C χ) = _
    rw [characterPoint_eval k C χ (toConv f * toConv g).ofConv]
    simp only [toConv_ofConv, map_mul, characterPoint_eval]

variable [IsAlgClosed k] [Nontrivial C] [Coalgebra.IsCocomm k C]

/-- No reducedness or characteristic restriction is needed for this group-like element. -/
theorem exists_groupLike : ∃ c : C, IsGroupLikeElem k c := by
  have : Module.Finite k (WithConv (Dual k C)) :=
    Module.Finite.of_surjective (WithConv.linearEquiv k (Dual k C)).symm.toLinearMap
      (WithConv.linearEquiv k (Dual k C)).symm.surjective
  obtain ⟨χ⟩ := AlgebraCharacter.exists_character k (WithConv (Dual k C))
  exact ⟨characterPoint k C χ, characterPoint_groupLike k C χ⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.CoalgebraGroupLike
