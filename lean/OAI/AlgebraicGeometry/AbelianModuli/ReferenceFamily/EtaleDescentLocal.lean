import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeSplitting
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Etale Descent Local -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent

noncomputable section

/-! Effective descent of actual morphisms and isomorphisms through the
constructed etale covers. Compatibility is equality on the actual kernel
pair, rather than an unexplained descent predicate. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S S' : Scheme} (u : S' ⟶ S)
  [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
  {X Y : Over S}

/-- Forget the local base change of the target after a local morphism. -/
def localUnderlyingMap (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Y) :
    (pullback X.hom u) ⟶ Y.left :=
  h.left ≫ pullback.fst Y.hom u

def Compatible (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Y) : Prop :=
  pullback.fst (pullback.fst X.hom u) (pullback.fst X.hom u) ≫ localUnderlyingMap u h =
    pullback.snd (pullback.fst X.hom u) (pullback.fst X.hom u) ≫ localUnderlyingMap u h

/-- An overlap-compatible local morphism descends uniquely, as a morphism
over the original base. -/
theorem exists_unique_morphism
    (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Y) (hc : Compatible u h) :
    ∃! q : X ⟶ Y, (Over.pullback u).map q = h := by
  let π := pullback.fst X.hom u
  have hcoeq : ∀ {W : Scheme} (a b : W ⟶ pullback X.hom u), a ≫ π = b ≫ π →
      a ≫ localUnderlyingMap u h = b ≫ localUnderlyingMap u h := by
    intro W a b hab
    let l := pullback.lift a b hab
    have hl := congrArg (fun k => l ≫ k) hc
    simpa only [Compatible, localUnderlyingMap, l, π, Category.assoc,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc] using hl
  let q := EffectiveEpi.desc π (localUnderlyingMap u h) hcoeq
  have hq : π ≫ q = localUnderlyingMap u h := EffectiveEpi.fac _ _ _
  have hbase : q ≫ Y.hom = X.hom := by
    apply (cancel_epi π).mp
    rw [← Category.assoc, hq]
    change (h.left ≫ pullback.fst Y.hom u) ≫ Y.hom = pullback.fst X.hom u ≫ X.hom
    rw [Category.assoc, pullback.condition]
    have hw : h.left ≫ pullback.snd Y.hom u = pullback.snd X.hom u := h.w
    rw [← Category.assoc, hw, pullback.condition]
  let q' : X ⟶ Y := Over.homMk q hbase
  have hmap : (Over.pullback u).map q' = h := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hq
    · exact (pullback.lift_snd _ _ _).trans h.w.symm
  refine ⟨q', hmap, ?_⟩
  intro r hr
  exact (Over.pullback u).map_injective (hr.trans hmap.symm)

/-- Compatible local isomorphisms descend effectively. The inverse is
descended as an actual morphism and the two inverse laws are proved by
faithfulness of pullback. -/
theorem exists_unique_iso
    (e : (Over.pullback u).obj X ≅ (Over.pullback u).obj Y)
    (hh : Compatible u e.hom) (hi : Compatible u e.inv) :
    ∃! q : X ≅ Y, (Over.pullback u).mapIso q = e := by
  obtain ⟨f, hf, _⟩ := exists_unique_morphism u e.hom hh
  obtain ⟨g, hg, _⟩ := exists_unique_morphism u e.inv hi
  have hfg : f ≫ g = 𝟙 X := by
    apply (Over.pullback u).map_injective
    rw [(Over.pullback u).map_comp, hf, hg, (Over.pullback u).map_id, e.hom_inv_id]
  have hgf : g ≫ f = 𝟙 Y := by
    apply (Over.pullback u).map_injective
    rw [(Over.pullback u).map_comp, hg, hf, (Over.pullback u).map_id, e.inv_hom_id]
  let q : X ≅ Y := ⟨f, g, hfg, hgf⟩
  refine ⟨q, Iso.ext hf, ?_⟩
  intro r hr
  apply Iso.ext
  apply (Over.pullback u).map_injective
  exact (congrArg Iso.hom hr).trans hf.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent
