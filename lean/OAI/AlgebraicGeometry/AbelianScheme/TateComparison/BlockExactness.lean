import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ProductActionDecomposition

/-! # Block Exactness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockExactness.ProductAction

noncomputable section

/-! Exact sequences remain exact on the actual idempotent ranges of a
product action. The quotient comparison retains the original maps. -/

variable {R M N P I : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  (θ : (I → R) →ₐ[R] Module.End R M) (ψ : (I → R) →ₐ[R] Module.End R N)
  (χ : (I → R) →ₐ[R] Module.End R P)
  (f : M →ₗ[R] N) (hf : ∀ a, f.comp (θ a) = (ψ a).comp f)
  (g : N →ₗ[R] P) (hg : ∀ a, g.comp (ψ a) = (χ a).comp g)

theorem blockMap_range (i : I) :
    (ProductActionDecomposition.ProductAction.blockMap θ ψ f hf i).range = f.range.comap (ProductActionDecomposition.ProductAction.block ψ i).subtype := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.val, congrArg Subtype.val hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟨ProductActionDecomposition.ProductAction.projector θ i x, ⟨x, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    have he := congrArg (fun a => a x) (hf (Pi.single i 1))
    change f (ProductActionDecomposition.ProductAction.projector θ i x) = ProductActionDecomposition.ProductAction.projector ψ i (f x) at he
    exact he.trans ((congrArg (ProductActionDecomposition.ProductAction.projector ψ i) hx).trans (ProductActionDecomposition.ProductAction.projector_on_block ψ i y))

theorem blockMap_ker (i : I) :
    (ProductActionDecomposition.ProductAction.blockMap θ ψ f hf i).ker = f.ker.comap (ProductActionDecomposition.ProductAction.block θ i).subtype := by
  ext x
  exact Subtype.ext_iff

theorem blockMap_exact (h : g.ker = f.range) (i : I) :
    (ProductActionDecomposition.ProductAction.blockMap ψ χ g hg i).ker = (ProductActionDecomposition.ProductAction.blockMap θ ψ f hf i).range := by
  rw [blockMap_ker, blockMap_range, h]

def blockMapRangeEquiv (i : I) :
    (ProductActionDecomposition.ProductAction.blockMap θ ψ f hf i).range ≃ₗ[R] ↥(f.range ⊓ ProductActionDecomposition.ProductAction.block ψ i) := by
  let e : f.range.comap (ProductActionDecomposition.ProductAction.block ψ i).subtype ≃ₗ[R] ↥(f.range ⊓ ProductActionDecomposition.ProductAction.block ψ i) := {
    toFun x := ⟨x.val.val, x.property, x.val.property⟩
    invFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  exact (LinearEquiv.ofEq _ _ (blockMap_range θ ψ f hf i)).trans e

def blockCokernelEquiv (h : g.ker = f.range) (i : I) :
    (ProductActionDecomposition.ProductAction.block ψ i ⧸ (ProductActionDecomposition.ProductAction.blockMap θ ψ f hf i).range) ≃ₗ[R] ↥(g.range ⊓ ProductActionDecomposition.ProductAction.block χ i) :=
  (Submodule.quotEquivOfEq _ _ (blockMap_exact θ ψ χ f hf g hg h i).symm).trans
    ((ProductActionDecomposition.ProductAction.blockMap ψ χ g hg i).quotKerEquivRange.trans (blockMapRangeEquiv ψ χ g hg i))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockExactness.ProductAction
