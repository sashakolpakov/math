import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ExactResidueCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockExactness

/-! # Block Tate Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockTateCoordinates.Construction

noncomputable section

/-!
Restricted evaluation on actual Tate blocks has precisely the uniformly
scaled block lattice as kernel. Surjectivity and the residue-coordinate
bijection are consequences of full Tate evaluation and the split action.
-/

variable (q : ℕ) [Fact q.Prime] {H I : Type*} [AddCommGroup H] (h : ℕ)
  (θ : (I → ℤ_[q]) →ₐ[ℤ_[q]] Module.End ℤ_[q] (TateComparison.Add.Tate.Module (H := H) q))
  (ψ : (I → ℤ_[q]) →ₐ[ℤ_[q]] Module.End ℤ_[q] (TateComparison.Add.Tate.torsion q H h))
  (heval : ∀ a, (TateComparison.Evaluation.Tate.evaluate q h).comp (θ a) = (ψ a).comp (TateComparison.Evaluation.Tate.evaluate q h))

theorem blockTateEvaluation_ker (i : I) :
    (TateComparison.ProductActionDecomposition.ProductAction.blockMap θ ψ (TateComparison.Evaluation.Tate.evaluate q h) heval i).ker =
      ((q : ℤ_[q]) ^ h • (LinearMap.id : TateComparison.ProductActionDecomposition.ProductAction.block θ i →ₗ[ℤ_[q]]
        TateComparison.ProductActionDecomposition.ProductAction.block θ i)).range := by
  let f : TateComparison.Add.Tate.Module (H := H) q →ₗ[ℤ_[q]] TateComparison.Add.Tate.Module (H := H) q :=
    (q : ℤ_[q]) ^ h • LinearMap.id
  have hf : ∀ a, f.comp (θ a) = (θ a).comp f := by
    intro a
    ext x
    simp only [f, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
  have hk : (TateComparison.Evaluation.Tate.evaluate (H := H) q h).ker = f.range := by
    ext x
    change TateComparison.Evaluation.Tate.evaluate q h x = 0 ↔ ∃ y, (q : ℤ_[q]) ^ h • y = x
    exact TateComparison.Evaluation.Tate.evaluate_eq_zero_iff q h x
  have hblock : TateComparison.ProductActionDecomposition.ProductAction.blockMap θ θ f hf i =
      (q : ℤ_[q]) ^ h • (LinearMap.id : TateComparison.ProductActionDecomposition.ProductAction.block θ i →ₗ[ℤ_[q]] TateComparison.ProductActionDecomposition.ProductAction.block θ i) := by
    ext x
    rfl
  rw [TateComparison.BlockExactness.ProductAction.blockMap_ker, hk, ← TateComparison.BlockExactness.ProductAction.blockMap_range θ θ f hf i, hblock]

theorem blockTateEvaluation_surjective (hdiv : ∀ x : H, ∃ y, q • y = x) (i : I) :
    Function.Surjective (TateComparison.ProductActionDecomposition.ProductAction.blockMap θ ψ (TateComparison.Evaluation.Tate.evaluate q h) heval i) :=
  TateComparison.ProductActionDecomposition.ProductAction.blockMap_surjective θ ψ (TateComparison.Evaluation.Tate.evaluate q h) heval
    (TateComparison.Evaluation.Tate.evaluate_surjective q hdiv h) i

set_option backward.isDefEq.respectTransparency false in
def blockTateTorsionCoordinates {d : ℕ} (hdiv : ∀ x : H, ∃ y, q • y = x) (i : I)
    (b : Module.Basis (Fin d) ℤ_[q] (TateComparison.ProductActionDecomposition.ProductAction.block θ i)) :
    TateComparison.ProductActionDecomposition.ProductAction.block ψ i ≃+ (Fin d → ZMod (q ^ h)) :=
  ExactResidueCoordinates.Construction.exactResidueCoordinates (V := TateComparison.ProductActionDecomposition.ProductAction.block θ i) (U := TateComparison.ProductActionDecomposition.ProductAction.block ψ i)
    (d := d) q b h (TateComparison.ProductActionDecomposition.ProductAction.blockMap θ ψ (TateComparison.Evaluation.Tate.evaluate q h) heval i)
    (blockTateEvaluation_surjective q h θ ψ heval hdiv i)
    (by
      rw [TateCoordinates.Construction.basisDiagonalSubmodule_const]
      exact blockTateEvaluation_ker q h θ ψ heval i)

theorem blockTateTorsionCoordinates_apply {d : ℕ} (hdiv : ∀ x : H, ∃ y, q • y = x) (i : I)
    (b : Module.Basis (Fin d) ℤ_[q] (TateComparison.ProductActionDecomposition.ProductAction.block θ i)) (x : TateComparison.ProductActionDecomposition.ProductAction.block θ i) :
    blockTateTorsionCoordinates q h θ ψ heval hdiv i b
      (TateComparison.ProductActionDecomposition.ProductAction.blockMap θ ψ (TateComparison.Evaluation.Tate.evaluate q h) heval i x) =
        IsogenyQuotient.Basis.Construction.basisCoordinateResidues q b (fun _ => h) x :=
  ExactResidueCoordinates.Construction.exactResidueCoordinates_apply _ _ _ _ _ _ x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockTateCoordinates.Construction
