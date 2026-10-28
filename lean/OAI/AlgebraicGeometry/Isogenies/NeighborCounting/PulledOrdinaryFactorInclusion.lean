import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitInclusionTransport

/-! # Pulled Ordinary Factor Inclusion -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.PulledOrdinaryFactorInclusion.Ordinary

/-! The chosen etale factor of the transported ordinary chart retains
the base-changed inclusion of the original integral factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitInclusionTransport

variable {S T : Scheme} (f : T ⟶ S) {M E A : Grp (Over S)} (s : M ⊗ E ≅ A)
  {M' E' : Grp (Over T)}
  (a : (Over.pullback f).mapGrp.obj M ≅ M')
  (b : (Over.pullback f).mapGrp.obj E ≅ E')

theorem pulledSplitSecond_inclusion :
    b.hom ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M' E' ≫
      ((Over.pullback f).mapGrp.mapIso s.symm ≪≫
        (Functor.Monoidal.μIso (Over.pullback f).mapGrp M E).symm ≪≫ tensorIso a b).inv =
      (Over.pullback f).mapGrp.map (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E ≫ s.hom) := by
  let F := (Over.pullback f).mapGrp
  let t := tensorIso a b
  let m := (Functor.Monoidal.μIso (Over.pullback f).mapGrp M E).hom
  let i := AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion (F.obj M) (F.obj E)
  have ht : i ≫ t.hom = b.hom ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M' E' :=
    SplitInclusionTransport.splitSecondInclusion_tensorIso (F.obj M) (F.obj E) a b
  have hm : F.map (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E) = i ≫ m :=
    SplitInclusionTransport.splitSecondInclusion_pullback f M E
  change b.hom ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M' E' ≫ (t.inv ≫ m ≫ F.map s.hom) = _
  calc
    b.hom ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M' E' ≫ (t.inv ≫ m ≫ F.map s.hom) =
        (b.hom ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M' E') ≫ t.inv ≫ m ≫ F.map s.hom := by
          simp only [Category.assoc]
    _ = (i ≫ t.hom) ≫ t.inv ≫ m ≫ F.map s.hom :=
      congrArg (fun u => u ≫ t.inv ≫ m ≫ F.map s.hom) ht.symm
    _ = i ≫ m ≫ F.map s.hom := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = F.map (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E) ≫ F.map s.hom :=
      (Category.assoc i m (F.map s.hom)).symm.trans
        (congrArg (fun u => u ≫ F.map s.hom) hm.symm)
    _ = F.map (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E ≫ s.hom) := (F.map_comp _ _).symm

end AlgebraicGeometry.Isogenies.NeighborCounting.PulledOrdinaryFactorInclusion.Ordinary

namespace AlgebraicGeometry.Isogenies.NeighborCounting.PulledOrdinaryFactorInclusion.TensorSubgroup

/-! Base change and the actual factor isomorphisms retain the inclusion
of a product subgroup in the transported ordinary chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S T : Scheme} (f : T ⟶ S)
  {M E A H : Grp (Over S)} (s : M ⊗ E ≅ A) (i : H ⟶ E)
  {M' E' H' : Grp (Over T)}
  (a : (Over.pullback f).mapGrp.obj M ≅ M')
  (b : (Over.pullback f).mapGrp.obj E ≅ E')
  (c : (Over.pullback f).mapGrp.obj H ≅ H') (j : H' ⟶ E')
  (hc : c.hom ≫ j = (Over.pullback f).mapGrp.map i ≫ b.hom)

include hc in
theorem pulledTensorSubgroup_inclusion :
    ((Functor.Monoidal.μIso (Over.pullback f).mapGrp M H).symm ≪≫ tensorIso a c).hom ≫
      ((𝟙 M') ⊗ₘ j) ≫
        ((Over.pullback f).mapGrp.mapIso s.symm ≪≫
          (Functor.Monoidal.μIso (Over.pullback f).mapGrp M E).symm ≪≫ tensorIso a b).inv =
      (Over.pullback f).mapGrp.map (((𝟙 M) ⊗ₘ i) ≫ s.hom) := by
  let F := (Over.pullback f).mapGrp
  let d := F.mapIso s.symm ≪≫ (Functor.Monoidal.μIso F M E).symm ≪≫ tensorIso a b
  change _ = F.map (((𝟙 M) ⊗ₘ i) ≫ s.hom)
  apply (cancel_mono d.hom).mp
  change (((Functor.Monoidal.μIso F M H).symm ≪≫ tensorIso a c).hom ≫
    ((𝟙 M') ⊗ₘ j) ≫ d.inv) ≫ d.hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Functor.OplaxMonoidal.δ F M H ≫ (a.hom ⊗ₘ c.hom) ≫ ((𝟙 M') ⊗ₘ j) =
    F.map (((𝟙 M) ⊗ₘ i) ≫ s.hom) ≫
      (F.map s.inv ≫ Functor.OplaxMonoidal.δ F M E ≫ (a.hom ⊗ₘ b.hom))
  have hs : F.map s.hom ≫ F.map s.inv = 𝟙 _ := (F.mapIso s).hom_inv_id
  rw [F.map_comp, Category.assoc, ← Category.assoc (F.map s.hom), hs, Category.id_comp,
    tensorHom_comp_tensorHom, Category.comp_id, hc]
  have ht : a.hom ⊗ₘ (F.map i ≫ b.hom) =
      (F.map (𝟙 M) ⊗ₘ F.map i) ≫ (a.hom ⊗ₘ b.hom) := by
    rw [tensorHom_comp_tensorHom, F.map_id, Category.id_comp]
  rw [ht, ← Category.assoc, Functor.OplaxMonoidal.δ_natural, Category.assoc]

end AlgebraicGeometry.Isogenies.NeighborCounting.PulledOrdinaryFactorInclusion.TensorSubgroup

end

end OAI
