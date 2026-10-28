import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateAction

/-! # Product Action Decomposition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ProductActionDecomposition.ProductAction

noncomputable section

section

/-! A finite product-ring action decomposes its actual module into the
ranges of its orthogonal projectors. The decomposition and eigenvalue
equations are proved from the algebra action. -/

open scoped BigOperators

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (θ : (I → R) →ₐ[R] Module.End R M)

def projector (i : I) : Module.End R M := by
  classical
  exact θ (Pi.single i 1)

theorem projector_eq_single [DecidableEq I] (i : I) : projector θ i = θ (Pi.single i 1) := by
  unfold projector
  congr 1
  ext j
  by_cases h : j = i <;> simp [h]

theorem projector_self (i : I) : projector θ i * projector θ i = projector θ i := by
  classical
  unfold projector
  rw [← map_mul]
  congr 1
  ext j
  by_cases h : j = i <;> simp [h]

theorem projector_orthogonal {i j : I} (h : i ≠ j) : projector θ i * projector θ j = 0 := by
  classical
  unfold projector
  rw [← map_mul, ← map_zero θ]
  congr 1
  ext k
  by_cases hi : k = i
  · subst k
    simp [h]
  · simp [Pi.single_apply, hi]

theorem sum_projector [Fintype I] : ∑ i, projector θ i = 1 := by
  classical
  unfold projector
  rw [← map_sum, ← map_one θ]
  congr 1
  ext i
  simp [Pi.single_apply]

def block (i : I) : Submodule R M := (projector θ i).range

theorem projector_on_block (i : I) (x : block θ i) : projector θ i x.val = x.val := by
  obtain ⟨y, hy⟩ := x.property
  change projector θ i y = x.val at hy
  rw [← hy]
  exact congrArg (fun f : Module.End R M => f y) (projector_self θ i)

theorem projector_on_other_block {i j : I} (h : i ≠ j) (x : block θ j) :
    projector θ i x.val = 0 := by
  obtain ⟨y, hy⟩ := x.property
  change projector θ j y = x.val at hy
  rw [← hy]
  exact congrArg (fun f : Module.End R M => f y) (projector_orthogonal θ h)

def decomposition [Fintype I] : M ≃ₗ[R] ∀ i, block θ i where
  toFun x i := ⟨projector θ i x, ⟨x, rfl⟩⟩
  invFun x := ∑ i, (x i).val
  left_inv x := by
    have h := congrArg (fun f : Module.End R M => f x) (sum_projector θ)
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using h
  right_inv x := by
    classical
    funext i
    apply Subtype.ext
    change projector θ i (∑ j, (x j).val) = (x i).val
    rw [map_sum, Finset.sum_eq_single i]
    · exact projector_on_block θ i (x i)
    · intro j _ hji
      exact projector_on_other_block θ hji.symm (x j)
    · simp
  map_add' x y := by funext i; exact Subtype.ext ((projector θ i).map_add x y)
  map_smul' r x := by funext i; exact Subtype.ext ((projector θ i).map_smul r x)

theorem action_on_block (a : I → R) (i : I) (x : block θ i) : θ a x.val = a i • x.val := by
  classical
  have hm : a * Pi.single i 1 = a i • (Pi.single i 1 : I → R) := by
    ext j
    by_cases h : j = i <;> simp [h]
  have he : θ a * projector θ i = a i • projector θ i := by
    change θ a * θ (Pi.single i 1) = a i • θ (Pi.single i 1)
    rw [← map_mul, hm, map_smul]
  have hx := congrArg (fun f : Module.End R M => f x.val) he
  change θ a (projector θ i x.val) = a i • projector θ i x.val at hx
  rwa [projector_on_block] at hx

theorem mem_block_iff (i : I) (x : M) : x ∈ block θ i ↔ ∀ a : I → R, θ a x = a i • x := by
  constructor
  · intro hx a
    exact action_on_block θ a i ⟨x, hx⟩
  · intro hx
    classical
    have he := hx (Pi.single i 1)
    change projector θ i x = (Pi.single i 1 : I → R) i • x at he
    simp only [Pi.single_eq_same, one_smul] at he
    exact ⟨x, he⟩

end

/-! Equivariant maps preserve the actual projector ranges. Their maps
on blocks retain the same underlying linear maps and compose correctly. -/

variable {R M N P I : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  (θ : (I → R) →ₐ[R] Module.End R M) (ψ : (I → R) →ₐ[R] Module.End R N)

def blockMap (f : M →ₗ[R] N) (hf : ∀ a, f.comp (θ a) = (ψ a).comp f) (i : I) :
    block θ i →ₗ[R] block ψ i :=
  (f.comp (block θ i).subtype).codRestrict (block ψ i) (by
    intro x
    obtain ⟨y, hy⟩ := x.property
    classical
    have he := congrArg (fun z => z y) (hf (Pi.single i 1))
    change f (projector θ i y) = projector ψ i (f y) at he
    exact ⟨f y, he.symm.trans (congrArg f hy)⟩)

theorem blockMap_val (f : M →ₗ[R] N) (hf : ∀ a, f.comp (θ a) = (ψ a).comp f)
    (i : I) (x : block θ i) : (blockMap θ ψ f hf i x).val = f x.val := rfl

theorem blockMap_surjective (f : M →ₗ[R] N) (hf : ∀ a, f.comp (θ a) = (ψ a).comp f)
    (hs : Function.Surjective f) (i : I) : Function.Surjective (blockMap θ ψ f hf i) := by
  intro z
  obtain ⟨x, hx⟩ := hs z.val
  refine ⟨⟨projector θ i x, ⟨x, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  classical
  have he := congrArg (fun a => a x) (hf (Pi.single i 1))
  change f (projector θ i x) = projector ψ i (f x) at he
  exact he.trans ((congrArg (projector ψ i) hx).trans (projector_on_block ψ i z))

theorem blockMap_injective (f : M →ₗ[R] N) (hf : ∀ a, f.comp (θ a) = (ψ a).comp f)
    (hi : Function.Injective f) (i : I) : Function.Injective (blockMap θ ψ f hf i) := by
  intro x y hxy
  apply Subtype.ext
  exact hi (congrArg Subtype.val hxy)

theorem blockMap_comp (χ : (I → R) →ₐ[R] Module.End R P)
    (f : M →ₗ[R] N) (hf : ∀ a, f.comp (θ a) = (ψ a).comp f)
    (g : N →ₗ[R] P) (hg : ∀ a, g.comp (ψ a) = (χ a).comp g) (i : I) :
    (blockMap ψ χ g hg i).comp (blockMap θ ψ f hf i) =
      blockMap θ χ (g.comp f) (fun a => by
        rw [LinearMap.comp_assoc, hf a, ← LinearMap.comp_assoc, hg a, LinearMap.comp_assoc]) i := by
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ProductActionDecomposition.ProductAction
