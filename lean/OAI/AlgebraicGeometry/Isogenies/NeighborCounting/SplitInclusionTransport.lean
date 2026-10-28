import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AnnihilatorSheaf
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupPullbackComposition

/-! # Split Inclusion Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitInclusionTransport

noncomputable section

/-! Product-factor inclusions commute with the actual group pullback
comparison and with isomorphisms of the two ordinary factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable {S T : Scheme} (f : T ⟶ S) (M E : Grp (Over S))

theorem splitSecondInclusion_pullback :
    (Over.pullback f).mapGrp.map (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E) =
      AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion ((Over.pullback f).mapGrp.obj M) ((Over.pullback f).mapGrp.obj E) ≫
        (Functor.Monoidal.μIso (Over.pullback f).mapGrp M E).hom := by
  apply Grp.hom_ext
  change (Over.pullback f).map (lift (1 : E.X ⟶ M.X) (𝟙 E.X)) =
    lift (1 : (Over.pullback f).obj E.X ⟶ (Over.pullback f).obj M.X)
      (𝟙 ((Over.pullback f).obj E.X)) ≫ Functor.LaxMonoidal.μ (Over.pullback f) M.X E.X
  rw [← Functor.Monoidal.lift_μ, (Over.pullback f).map_one, (Over.pullback f).map_id]

theorem splitSecondInclusion_tensorIso {M' E' : Grp (Over S)} (a : M ≅ M') (b : E ≅ E') :
    AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E ≫ (tensorIso a b).hom = b.hom ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M' E' := by
  apply Grp.hom_ext
  change lift (1 : E.X ⟶ M.X) (𝟙 E.X) ≫ (a.hom.hom.hom ⊗ₘ b.hom.hom.hom) =
    b.hom.hom.hom ≫ lift (1 : E'.X ⟶ M'.X) (𝟙 E'.X)
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd, lift_fst_assoc,
      lift_snd_assoc, lift_fst, lift_snd, MonObj.one_comp, MonObj.comp_one,
      Category.id_comp, Category.comp_id]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitInclusionTransport
