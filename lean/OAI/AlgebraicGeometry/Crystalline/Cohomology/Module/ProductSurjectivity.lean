import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # Product Surjectivity -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.ProductSurjectivity.ModuleProductSurjectivity

noncomputable section

/-!
# Surjectivity of products of module maps

Componentwise preimages assemble in the actual categorical product.
This applies in the larger coefficient universe used by native sheaves.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {R : Type u} [Ring R] {ι : Type v}
  (A B : ι → ModuleCat.{max v w} R) [HasProduct A] [HasProduct B]
  (f : ∀ i, A i ⟶ B i)

theorem surjective (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (Limits.Pi.map f) := by
  intro z
  let y : ∀ i, A i := fun i => (hf i (Pi.π B i z)).choose
  have hy : ∀ i, f i (y i) = Pi.π B i z := fun i => (hf i (Pi.π B i z)).choose_spec
  refine ⟨(ModuleCat.piIsoPi A).inv y, ?_⟩
  apply Concrete.limit_ext (Discrete.functor B)
  intro i
  have hm := congrArg (fun g => g ((ModuleCat.piIsoPi A).inv y)) (Pi.map_π f i.as)
  have hp := congrArg (fun g => g y) (ModuleCat.piIsoPi_inv_kernel_ι A i.as)
  exact hm.trans ((congrArg (f i.as) hp).trans (hy i.as))

theorem epi (hf : ∀ i, Epi (f i)) : Epi (Limits.Pi.map f) :=
  (ModuleCat.epi_iff_surjective _).mpr
    (surjective A B f (fun i => (ModuleCat.epi_iff_surjective (f i)).mp (hf i)))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.ProductSurjectivity.ModuleProductSurjectivity
