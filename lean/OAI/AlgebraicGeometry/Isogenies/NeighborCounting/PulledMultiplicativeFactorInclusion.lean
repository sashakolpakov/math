import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductFactorMaps
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupPullbackComposition

/-! # Pulled Multiplicative Factor Inclusion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PulledMultiplicativeFactorInclusion

noncomputable section

/-! The original multiplicative factor retains its inclusion through
the actual base-change and ordinary-chart isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupPullbackComposition.Construction
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

section
variable {S T : Scheme} (f : T ⟶ S) (M E : Grp (Over S))

theorem splitFirstInclusion_pullback :
    (Over.pullback f).mapGrp.map (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M E) =
      AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion ((Over.pullback f).mapGrp.obj M) ((Over.pullback f).mapGrp.obj E) ≫
        (Functor.Monoidal.μIso (Over.pullback f).mapGrp M E).hom := by
  apply Grp.hom_ext
  change (Over.pullback f).map (lift (𝟙 M.X) (1 : M.X ⟶ E.X)) =
    lift (𝟙 ((Over.pullback f).obj M.X))
      (1 : (Over.pullback f).obj M.X ⟶ (Over.pullback f).obj E.X) ≫ Functor.LaxMonoidal.μ (Over.pullback f) M.X E.X
  rw [← Functor.Monoidal.lift_μ, (Over.pullback f).map_one, (Over.pullback f).map_id]

end

variable {S T : Scheme} (f : T ⟶ S) {M E A : Grp (Over S)} (s : M ⊗ E ≅ A)
  {M' E' : Grp (Over T)}
  (a : (Over.pullback f).mapGrp.obj M ≅ M')
  (b : (Over.pullback f).mapGrp.obj E ≅ E')

theorem pulledSplitFirst_inclusion :
    a.hom ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M' E' ≫
      ((Over.pullback f).mapGrp.mapIso s.symm ≪≫
        (Functor.Monoidal.μIso (Over.pullback f).mapGrp M E).symm ≪≫ tensorIso a b).inv =
      (Over.pullback f).mapGrp.map (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M E ≫ s.hom) := by
  let F := (Over.pullback f).mapGrp
  let t := tensorIso a b
  let m := (Functor.Monoidal.μIso (Over.pullback f).mapGrp M E).hom
  let i := AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion (F.obj M) (F.obj E)
  have ht : i ≫ t.hom = a.hom ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M' E' :=
    GroupProductFactorMaps.splitFirstInclusion_tensorHom a.hom b.hom
  have hm : F.map (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M E) = i ≫ m :=
    splitFirstInclusion_pullback f M E
  change a.hom ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M' E' ≫ (t.inv ≫ m ≫ F.map s.hom) = _
  calc
    a.hom ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M' E' ≫ (t.inv ≫ m ≫ F.map s.hom) =
        (a.hom ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M' E') ≫ t.inv ≫ m ≫ F.map s.hom := by
          simp only [Category.assoc]
    _ = (i ≫ t.hom) ≫ t.inv ≫ m ≫ F.map s.hom :=
      congrArg (fun u => u ≫ t.inv ≫ m ≫ F.map s.hom) ht.symm
    _ = i ≫ m ≫ F.map s.hom := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = F.map (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M E) ≫ F.map s.hom :=
      (Category.assoc i m (F.map s.hom)).symm.trans
        (congrArg (fun u => u ≫ F.map s.hom) hm.symm)
    _ = F.map (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion M E ≫ s.hom) := (F.map_comp _ _).symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PulledMultiplicativeFactorInclusion
