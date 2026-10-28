import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Cover Dense Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoverDenseSurjectivity.Construction

/-! Surjectivity on a cover-dense family gives local surjectivity on
the full site. This retains every test object after sheafification. -/

open _root_.CategoryTheory Opposite

universe u v w

variable {C D : Type*} [Category* C] [Category* D]
variable (J : GrothendieckTopology D) (H : C ⥤ D) [H.IsCoverDense J]
variable {F G : Dᵒᵖ ⥤ Type w} (a : F ⟶ G)
variable (hs : ∀ X : C, Function.Surjective (a.app (.op (H.obj X))))

include hs in
theorem locallySurjective_of_surjective_coverDense : Presheaf.IsLocallySurjective J a where
  imageSieve_mem {X} x := by
    apply J.superset_covering ?_ (H.is_cover_of_isCoverDense J X)
    rintro U t ⟨⟨V, u, v, rfl⟩⟩
    obtain ⟨y, hy⟩ := hs V (G.map v.op x)
    refine ⟨F.map u.op y, ?_⟩
    rw [op_comp, G.map_comp, ConcreteCategory.comp_apply, ← hy, NatTrans.naturality_apply]

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoverDenseSurjectivity.Construction
