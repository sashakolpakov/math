import OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicKernel

/-! # Compatible Reduced Kernels -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CompatibleReducedKernels.Construction

noncomputable section

/-!
# Completion: the inverse limit of the actual reduced differential kernels

Compatible zero-cycles modulo all powers of an ideal are the kernel of the
completed differential. For finite modules, Artin--Rees identifies this
with the completion of the original kernel, with the actual coordinate maps.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N)

/-- Compatible families in the kernels of the actual reduced differential. -/
def compatibleReducedKernels : Submodule R
    (∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  carrier := {x | (∀ {m n} (h : m ≤ n), AdicCompletion.transitionMap I M h (x n) = x m) ∧
    ∀ n, f.reduceModIdeal (I ^ n) (x n) = 0}
  zero_mem' := ⟨fun _ => map_zero _, fun _ => map_zero _⟩
  add_mem' hx hy := ⟨fun h => by simp only [Pi.add_apply, map_add, hx.1 h, hy.1 h],
    fun n => by simp only [Pi.add_apply, map_add, hx.2 n, hy.2 n, add_zero]⟩
  smul_mem' r x hx := ⟨fun h => by simp only [Pi.smul_apply, map_smul, hx.1 h],
    fun n => by
      change ((f.reduceModIdeal (I ^ n)).restrictScalars R) (r • x n) = 0
      rw [map_smul, LinearMap.restrictScalars_apply, hx.2 n, smul_zero]⟩

/-- Evaluation identifies the kernel of completion with compatible reduced kernels. -/
def completedKernelCompatibleEquiv :
    (AdicCompletion.map I f).ker ≃ₗ[R] compatibleReducedKernels I f where
  toFun x := ⟨x.val.val, x.val.property, fun n => by
    have h := congrArg (fun z : AdicCompletion I N => z.val n) x.property
    exact h⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, by
    apply AdicCompletion.ext
    exact x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical comparison from completed zero-cycles to all reduced zero-cycles. -/
def reducedKernelComparison :
    AdicCompletion I f.ker →ₗ[R] compatibleReducedKernels I f :=
  (completedKernelCompatibleEquiv I f).toLinearMap.comp
    ((AdicKernel.Construction.adicKernelMap I f).restrictScalars R)

theorem reducedKernelComparison_apply (x : AdicCompletion I f.ker) (n : ℕ) :
    (reducedKernelComparison I f x).val n =
      f.ker.subtype.reduceModIdeal (I ^ n) (x.val n) := rfl

/-- The finite-module formal zero-cycle comparison is surjective. -/
theorem reducedKernelComparison_bijective
    [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N] :
    Function.Bijective (reducedKernelComparison I f) :=
  (completedKernelCompatibleEquiv I f).bijective.comp (AdicKernel.Construction.adicKernelMap_bijective I f)

/-- Every compatible family of reduced zero-cycles comes from completed zero-cycles. -/
theorem exists_completedKernel_lift
    [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N]
    (x : ∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M))
    (hcompat : ∀ {m n} (h : m ≤ n), AdicCompletion.transitionMap I M h (x n) = x m)
    (hzero : ∀ n, f.reduceModIdeal (I ^ n) (x n) = 0) :
    ∃ y : AdicCompletion I f.ker,
      ∀ n, f.ker.subtype.reduceModIdeal (I ^ n) (y.val n) = x n := by
  obtain ⟨y, hy⟩ := (reducedKernelComparison_bijective I f).surjective ⟨x, hcompat, hzero⟩
  exact ⟨y, fun n => congrArg (fun z : compatibleReducedKernels I f => z.val n) hy⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CompatibleReducedKernels.Construction
