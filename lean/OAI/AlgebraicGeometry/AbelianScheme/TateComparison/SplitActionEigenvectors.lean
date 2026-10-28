import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitAction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ProductActionDecomposition

/-! # Split Action Eigenvectors -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The product-ring projector ranges are characterized by the original
integral characters. The good-prime completion proves the converse. -/

open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {M : Type*} [AddCommGroup M] [Module ℤ_[q] M]
  (θ : (Fin s × Bool → ℤ_[q]) →ₐ[ℤ_[q]] Module.End ℤ_[q] M)

include h in
theorem Data.SphericalPELAlbaneseData.block_mem_iff_characters (v : Fin s × Bool) (x : M) :
    x ∈ ProductActionDecomposition.ProductAction.block θ v ↔ ∀ r : NumberField.RingOfIntegers E,
      θ (fun w => D.localCharacter w r) x = D.localCharacter v r • x := by
  rw [ProductActionDecomposition.ProductAction.mem_block_iff]
  constructor
  · intro hx r
    exact hx (fun w => D.localCharacter w r)
  · intro hx a
    have he (z : ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E) :
        θ (D.localCompletionMapZq z) x = D.localCompletionMapZq z v • x := by
      induction z using TensorProduct.inductionOn with
      | tmul b r =>
        change θ (b • (fun w => D.localCharacter w r)) x =
          (b • (fun w => D.localCharacter w r)) v • x
        rw [map_smul, LinearMap.smul_apply, hx r]
        exact smul_smul b (D.localCharacter v r) x
      | add z z' hz hz' =>
        rw [map_add, map_add, LinearMap.add_apply, Pi.add_apply, add_smul, hz, hz']
    obtain ⟨z, hz⟩ := (D.localCompletionEquivZq h).surjective a
    change D.localCompletionMapZq z = a at hz
    rw [← hz]
    exact he z

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
