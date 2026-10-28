import OAI.RepresentationTheory.Theta.Geometric.LineBundleIsoGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff

/-! # Disjoint Line Iso Gluing -/

namespace OAI.RepresentationTheory.Theta.Geometric.DisjointLineIsoGluing

noncomputable section

/-! Actual module isomorphisms on disjoint open fibers glue, with their
native pullback restrictions retained. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

def openOverPullbackIso {X : Scheme.{u}} (U : X.Opens) :
    _root_.SheafOfModules.overFunctor X.ringCatSheaf U ⋙ (Scheme.Modules.overEquiv U).functor ≅
      Scheme.Modules.pullback U.ι :=
  Scheme.Modules.overFunctorEquiv U ≪≫ Scheme.Modules.restrictFunctorIsoPullback U.ι

def nativeOpenIsoToOver {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ (Scheme.Modules.pullback U.ι).obj N) :
    M.over U ≅ N.over U :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((openOverPullbackIso U).app M ≪≫ e ≪≫ ((openOverPullbackIso U).app N).symm)

theorem nativeOpenIsoToOver_restrict {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ (Scheme.Modules.pullback U.ι).obj N)
    (g : M ⟶ N) (hg : g.over U = (nativeOpenIsoToOver M N U e).hom) :
    (Scheme.Modules.pullback U.ι).map g = e.hom := by
  have h := (openOverPullbackIso U).hom.naturality g
  change (Scheme.Modules.overEquiv U).functor.map (g.over U) ≫
      ((openOverPullbackIso U).app N).hom =
    ((openOverPullbackIso U).app M).hom ≫ (Scheme.Modules.pullback U.ι).map g at h
  rw [hg] at h
  simp only [nativeOpenIsoToOver, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  exact ((cancel_epi ((openOverPullbackIso U).app M).hom).mp h).symm

theorem overModuleHom_eq_of_empty {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens) (hU : U = ⊥) (f g : M.over U ⟶ N.over U) : f = g := by
  let F : TopCat.Sheaf (Type u) X := AlgebraicGeometry.SheafCohomology.Projective.LinearHom.linearHomSheaf X.ringCatSheaf M N
  let : Unique (F.obj.obj (op U)) :=
    Limits.Types.isTerminalEquivUnique _ (F.isTerminalOfEqEmpty hU)
  have h : AlgebraicGeometry.SheafCohomology.Projective.ModuleHomGluing.linearHomLocalSection M N U f = AlgebraicGeometry.SheafCohomology.Projective.ModuleHomGluing.linearHomLocalSection M N U g := Subsingleton.elim _ _
  apply (_root_.SheafOfModules.toSheaf (X.ringCatSheaf.over U)).map_injective
  exact congrArg Subtype.val h

theorem exists_moduleIso_of_disjoint_open_cover {X : Scheme.{u}} (M N : X.Modules)
    {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤)
    (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥)
    (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ≅ (Scheme.Modules.pullback (U i).ι).obj N) :
    ∃ g : M ≅ N, ∀ i, (Scheme.Modules.pullback (U i).ι).map g.hom = (e i).hom := by
  obtain ⟨g, hg⟩ := LineBundleIsoGluing.exists_moduleIso_of_localIsos M N U hU
    (fun i => nativeOpenIsoToOver M N (U i) (e i)) (by
      intro i j
      by_cases hij : i = j
      · subst j
        rfl
      · exact overModuleHom_eq_of_empty M N (U i ⊓ U j) (hdisj i j hij) _ _)
  exact ⟨g, fun i => nativeOpenIsoToOver_restrict M N (U i) (e i) g.hom (hg i)⟩

theorem exists_moduleIso_on_locallyConstant_fibers {X : Scheme.{u}} (M N : X.Modules)
    {I : Type u} (c : LocallyConstant X I)
    (e : ∀ i, (Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c i).ι).obj M ≅
      (Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c i).ι).obj N) :
    ∃ g : M ≅ N, ∀ i,
      (Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c i).ι).map g.hom = (e i).hom := by
  apply exists_moduleIso_of_disjoint_open_cover M N (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c) _ _ e
  · apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨c x, rfl⟩
  · intro i j hij
    apply le_bot_iff.mp
    intro x hx
    exact (hij (hx.1.symm.trans hx.2)).elim

end

end OAI.RepresentationTheory.Theta.Geometric.DisjointLineIsoGluing
