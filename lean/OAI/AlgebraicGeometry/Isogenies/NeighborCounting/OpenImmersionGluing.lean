import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DisjointOpenGluing
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsoDescent

/-! # Open Immersion Gluing -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenImmersionGluing

noncomputable section

/-! Gluing along disjoint open immersions, retaining their given source
schemes and the exact pullback isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DisjointOpenGluing

theorem pullbackHomTo_map {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : X ⟶ Z) (h : f ≫ g = p) {M N : Z.Modules} (q : M ⟶ N) :
    FramedPullback.pullbackHomTo f g p h ((Scheme.Modules.pullback g).map q) =
      (Scheme.Modules.pullback p).map q := by
  let c := Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h
  have hn := c.hom.naturality q
  exact (congrArg (fun a ↦ (c.app M).inv ≫ a) hn).trans ((c.app M).inv_hom_id_assoc _)

theorem pullbackHomTo_injective {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : X ⟶ Z) (h : f ≫ g = p) {M N : Z.Modules}
    [(Scheme.Modules.pullback f).Faithful] :
    Function.Injective (FramedPullback.pullbackHomTo (M := M) (N := N) f g p h) := by
  intro a b hab
  apply (Scheme.Modules.pullback f).map_injective
  let c := Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr h
  exact ((c.app M).homCongr (c.app N)).injective hab

variable {X Y : Scheme.{u}} {M N : Y.Modules} (f : X ⟶ Y) [IsOpenImmersion f]

def isoOnRange (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N) :
    (Scheme.Modules.pullback f.opensRange.ι).obj M ≅ (Scheme.Modules.pullback f.opensRange.ι).obj N :=
  FramedPullback.pullbackIsoTo f.isoOpensRange.inv f f.opensRange.ι f.isoOpensRange_inv_comp e

theorem isoOnRange_mapIso (d : M ≅ N) :
    isoOnRange f ((Scheme.Modules.pullback f).mapIso d) =
      (Scheme.Modules.pullback f.opensRange.ι).mapIso d := by
  apply Iso.ext
  exact (FramedPullback.pullbackIsoTo_hom f.isoOpensRange.inv f f.opensRange.ι f.isoOpensRange_inv_comp
    ((Scheme.Modules.pullback f).mapIso d)).trans
      (pullbackHomTo_map f.isoOpensRange.inv f f.opensRange.ι f.isoOpensRange_inv_comp d.hom)

theorem isoOnRange_injective : Function.Injective (isoOnRange (M := M) (N := N) f) := by
  intro e d hed
  have : (Scheme.Modules.pullback f.isoOpensRange.inv).IsEquivalence :=
    Picard.PoincareBundle.IsoDescent.pullback_isEquivalence f.isoOpensRange.symm
  apply Iso.ext
  apply pullbackHomTo_injective f.isoOpensRange.inv f f.opensRange.ι f.isoOpensRange_inv_comp
  exact (FramedPullback.pullbackIsoTo_hom f.isoOpensRange.inv f f.opensRange.ι f.isoOpensRange_inv_comp e).symm.trans
    ((congrArg Iso.hom hed).trans
      (FramedPullback.pullbackIsoTo_hom f.isoOpensRange.inv f f.opensRange.ι f.isoOpensRange_inv_comp d))

omit f [IsOpenImmersion f] in
theorem existsUnique_disjoint_immersion_iso {ι : Type*} (T : ι → Scheme.{u}) (a : ∀ i, T i ⟶ Y)
    [∀ i, IsOpenImmersion (a i)]
    (hU : (⊤ : Y.Opens) ≤ ⨆ i, (a i).opensRange)
    (hd : Pairwise (fun i j ↦ Disjoint (a i).opensRange (a j).opensRange))
    (e : ∀ i, (Scheme.Modules.pullback (a i)).obj M ≅ (Scheme.Modules.pullback (a i)).obj N) :
    ∃! d : M ≅ N, ∀ i, (Scheme.Modules.pullback (a i)).mapIso d = e i := by
  obtain ⟨d, hd, hu⟩ := DisjointOpenGluing.existsUnique_disjoint_iso M N (fun i ↦ (a i).opensRange) hU hd
    (fun i ↦ isoOnRange (a i) (e i))
  refine ⟨d, ?_, ?_⟩
  · intro i
    apply isoOnRange_injective (a i)
    exact (isoOnRange_mapIso (a i) d).trans (hd i)
  · intro d' hd'
    apply hu
    intro i
    exact (isoOnRange_mapIso (a i) d').symm.trans (congrArg (isoOnRange (a i)) (hd' i))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenImmersionGluing
