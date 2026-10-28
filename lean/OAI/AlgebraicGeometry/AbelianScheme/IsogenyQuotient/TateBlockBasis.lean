import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockTateCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteGeneration

/-! # Tate Block Basis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateBlockBasis.Construction

noncomputable section

/-!
Integral Tate blocks are finite free. Their finite-level point counts
determine their ranks through the actual evaluation coordinates, so a
rank-three basis is constructed once the q-torsion block has q^3 points.
-/

variable (q : ℕ) [Fact q.Prime] {H I : Type*} [AddCommGroup H]
  [Finite (TateComparison.Add.Tate.torsion q H 1)] (hdiv : ∀ x : H, ∃ y, q • y = x)
  (θ : (I → ℤ_[q]) →ₐ[ℤ_[q]] Module.End ℤ_[q] (TateComparison.Add.Tate.Module (H := H) q)) (i : I)

include hdiv in
theorem integralTateBlock_finite : Module.Finite ℤ_[q] (TateComparison.ProductActionDecomposition.ProductAction.block θ i) := by
  have := TateComparison.FiniteGeneration.Tate.finite_of_finite_torsion q hdiv
  infer_instance

include hdiv in
theorem integralTateBlock_free : Module.Free ℤ_[q] (TateComparison.ProductActionDecomposition.ProductAction.block θ i) := by
  have := integralTateBlock_finite q hdiv θ i
  have : Module.IsTorsionFree ℤ_[q] (TateComparison.ProductActionDecomposition.ProductAction.block θ i) :=
    Module.IsTorsionFree.of_smul_eq_zero fun (r : ℤ_[q]) (x : TateComparison.ProductActionDecomposition.ProductAction.block θ i) hx => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · apply Or.inr
        apply Subtype.ext
        exact TateComparison.Functor.Tate.smul_eq_zero_of_ne_zero q r hr x.val (congrArg Subtype.val hx)
  exact Module.free_of_finite_type_torsion_free' (R := ℤ_[q]) (M := TateComparison.ProductActionDecomposition.ProductAction.block θ i)

def integralTateBlockBasis :
    Module.Basis (Fin (Module.finrank ℤ_[q] (TateComparison.ProductActionDecomposition.ProductAction.block θ i)))
      ℤ_[q] (TateComparison.ProductActionDecomposition.ProductAction.block θ i) := by
  have := integralTateBlock_finite q hdiv θ i
  have := integralTateBlock_free q hdiv θ i
  exact Module.finBasis _ _

variable (n : ℕ)
  (ψ : (I → ℤ_[q]) →ₐ[ℤ_[q]] Module.End ℤ_[q] (TateComparison.Add.Tate.torsion q H n))
  (heval : ∀ a, (TateComparison.Evaluation.Tate.evaluate q n).comp (θ a) = (ψ a).comp (TateComparison.Evaluation.Tate.evaluate q n))

include hdiv heval in
theorem finiteTateBlock_card :
    Nat.card (TateComparison.ProductActionDecomposition.ProductAction.block ψ i) = (q ^ n) ^ Module.finrank ℤ_[q] (TateComparison.ProductActionDecomposition.ProductAction.block θ i) := by
  let B := integralTateBlockBasis q hdiv θ i
  let e := BlockTateCoordinates.Construction.blockTateTorsionCoordinates q n θ ψ heval hdiv i B
  calc
    Nat.card (TateComparison.ProductActionDecomposition.ProductAction.block ψ i) =
        Nat.card (Fin (Module.finrank ℤ_[q] (TateComparison.ProductActionDecomposition.ProductAction.block θ i)) → ZMod (q ^ n)) :=
      Nat.card_congr e.toEquiv
    _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

variable (ψ₁ : (I → ℤ_[q]) →ₐ[ℤ_[q]] Module.End ℤ_[q] (TateComparison.Add.Tate.torsion q H 1))
  (heval₁ : ∀ a, (TateComparison.Evaluation.Tate.evaluate q 1).comp (θ a) = (ψ₁ a).comp (TateComparison.Evaluation.Tate.evaluate q 1))

include hdiv heval₁ in
theorem integralTateBlock_rank_of_card (d : ℕ) (hd : Nat.card (TateComparison.ProductActionDecomposition.ProductAction.block ψ₁ i) = q ^ d) :
    Module.finrank ℤ_[q] (TateComparison.ProductActionDecomposition.ProductAction.block θ i) = d := by
  have he := (finiteTateBlock_card q hdiv θ i 1 ψ₁ heval₁).symm.trans hd
  rw [pow_one] at he
  exact Nat.pow_right_injective (Fact.out : q.Prime).two_le he

def rankThreeTateBlockBasis (hd : Nat.card (TateComparison.ProductActionDecomposition.ProductAction.block ψ₁ i) = q ^ 3) :
    Module.Basis (Fin 3) ℤ_[q] (TateComparison.ProductActionDecomposition.ProductAction.block θ i) :=
  (integralTateBlockBasis q hdiv θ i).reindex
    (finCongr (integralTateBlock_rank_of_card q hdiv θ i ψ₁ heval₁ 3 hd))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateBlockBasis.Construction
