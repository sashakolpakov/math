import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HilbertFamilyOfImmersion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HomFunctor

/-! # Fiber Hilbert Family -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.FiberHilbertFamily

noncomputable section

section

/-! The graph of a finite flat cover is the actual Hilbert family
of its fibers inside the covering scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem schemeSeparatedGraph_closed {B V W : Scheme.{0}} (p : V ⟶ B) (f : W ⟶ B)
    [IsSeparated f] (g : V ⟶ W) (hg : g ≫ f = p) :
    IsClosedImmersion (pullback.lift (𝟙 V) g (by simpa using hg.symm)) := by
  subst p
  exact inferInstanceAs
    (IsClosedImmersion (pullback.lift (𝟙 V) g (Category.id_comp (g ≫ f))))

variable {S : Scheme.{0}} {X Y : Over S} (q : X ⟶ Y)

def fiberGraph : X ⟶ Y ⨯ X := prod.lift q (𝟙 X)

theorem fiberGraph_projection :
    (fiberGraph q).left ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X Y = q.left := by
  change (fiberGraph q).left ≫ (prod.fst : Y ⨯ X ⟶ Y).left = _
  rw [← Over.comp_left, fiberGraph, prod.lift_fst]

theorem fiberGraph_closed [IsSeparated Y.hom] : IsClosedImmersion (fiberGraph q).left := by
  let e := Over.prodLeftIsoPullback Y X ≪≫ pullbackSymmetry Y.hom X.hom
  have h : (fiberGraph q).left ≫ e.hom =
      pullback.lift (𝟙 X.left) q.left (by simp) := by
    apply pullback.hom_ext
    · simp only [e, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst,
        Over.prodLeftIsoPullback_hom_snd, ← Over.comp_left, fiberGraph, prod.lift_snd,
        pullback.lift_fst, Over.id_left]
    · simp only [e, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
        Over.prodLeftIsoPullback_hom_fst, ← Over.comp_left, fiberGraph, prod.lift_fst,
        pullback.lift_snd]
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ e.hom, h]
  exact schemeSeparatedGraph_closed X.hom Y.hom q.left q.w

def finiteFiberHilbertFamily [IsSeparated Y.hom]
    [IsFinite q.left] [Flat q.left] [LocallyOfFinitePresentation q.left] : HilbertScheme.Presentations.Hilbert.Functor.Family X Y := by
  have : IsClosedImmersion (fiberGraph q).left := fiberGraph_closed q
  have : Flat ((fiberGraph q).left ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X Y) :=
    (fiberGraph_projection q).symm ▸ inferInstanceAs (Flat q.left)
  have : IsProper ((fiberGraph q).left ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X Y) :=
    (fiberGraph_projection q).symm ▸ inferInstanceAs (IsProper q.left)
  have : LocallyOfFinitePresentation ((fiberGraph q).left ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X Y) :=
    (fiberGraph_projection q).symm ▸ inferInstanceAs (LocallyOfFinitePresentation q.left)
  exact HilbertFamilyOfImmersion.hilbertFamilyOfClosedImmersion X Y (fiberGraph q).left

end

/-! The Hilbert family of fibers of a faithfully flat cover separates
all maps to its target, including maps from nonreduced schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {X Y T V : Over S} (q : X ⟶ Y) [IsSeparated Y.hom]

theorem fiberGraph_relation_of_equal_pullbacks (h k : T ⟶ Y)
    (he : (fiberGraph q).left.ker.comap (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X h) =
      (fiberGraph q).left.ker.comap (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X k))
    (a : V ⟶ T) (z : V ⟶ X) (hz : z ≫ q = a ≫ h) : z ≫ q = a ≫ k := by
  let j := prod.lift a z
  have hj : j ≫ prod.map h (𝟙 X) = z ≫ fiberGraph q := by
    apply prod.hom_ext <;> simp [j, fiberGraph, hz]
  have hle : (fiberGraph q).left.ker ≤ (j.left ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X h).ker := by
    change (fiberGraph q).left.ker ≤ (j ≫ prod.map h (𝟙 X)).left.ker
    rw [hj]
    exact z.left.le_ker_comp (fiberGraph q).left
  have hb : ((fiberGraph q).left.ker.comap (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X h)).comap j.left ≤ ⊥ := by
    have H : (fiberGraph q).left.ker ≤
        (⊥ : V.left.IdealSheafData).map (j.left ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X h) := by
      simpa only [Scheme.IdealSheafData.map_bot] using hle
    have H' := Scheme.IdealSheafData.le_map_iff_comap_le.mp H
    rw [Scheme.IdealSheafData.comap_comp] at H'
    exact H'
  rw [he] at hb
  have hk : (fiberGraph q).left.ker ≤ (j.left ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X k).ker := by
    have H : (fiberGraph q).left.ker.comap (j.left ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X k) ≤
        (⊥ : V.left.IdealSheafData) := by
      rw [Scheme.IdealSheafData.comap_comp]
      exact hb
    simpa only [Scheme.IdealSheafData.map_bot] using
      (Scheme.IdealSheafData.le_map_iff_comap_le.mpr H)
  have : IsClosedImmersion (fiberGraph q).left := fiberGraph_closed q
  let m := IsClosedImmersion.lift (fiberGraph q).left (j.left ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X k) hk
  have hm : m ≫ (fiberGraph q).left = j.left ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X k :=
    IsClosedImmersion.lift_fac _ _ _
  have hms : m = z.left := by
    have H := congrArg (fun t => t ≫ (prod.snd : Y ⨯ X ⟶ X).left) hm
    simpa only [Category.assoc, ← Over.comp_left, fiberGraph, prod.lift_snd,
      Over.id_left, Category.comp_id, HilbertScheme.Presentations.Hilbert.Functor.ambientMap, prod.map_snd, prod.lift_snd_assoc,
      j] using H
  apply Over.OverMorphism.ext
  have H := congrArg (fun t => t ≫ (prod.fst : Y ⨯ X ⟶ Y).left) hm
  simpa only [hms, Category.assoc, ← Over.comp_left, fiberGraph, prod.lift_fst,
    HilbertScheme.Presentations.Hilbert.Functor.ambientMap, prod.map_fst, prod.lift_fst_assoc, j] using H

theorem fiberGraph_pullback_injective [Flat q.left] [Surjective q.left] (T : Over S) :
    Function.Injective (fun h : T ⟶ Y => (fiberGraph q).left.ker.comap (HilbertScheme.Presentations.Hilbert.Functor.ambientMap X h)) := by
  intro h k he
  let W := pullback q h
  let a : W ⟶ T := pullback.snd q h
  let z : W ⟶ X := pullback.fst q h
  have hc := (IsPullback.of_hasPullback q h).map (Over.forget S)
  have : Flat a.left := MorphismProperty.of_isPullback hc (inferInstanceAs (Flat q.left))
  have : Surjective a.left := MorphismProperty.of_isPullback hc (inferInstanceAs (Surjective q.left))
  have : Epi a.left := Flat.epi_of_flat_of_surjective a.left
  have hcq : z ≫ q = a ≫ h := pullback.condition
  have H := fiberGraph_relation_of_equal_pullbacks q h k he a z hcq
  apply Over.OverMorphism.ext
  apply (cancel_epi a.left).mp
  exact congrArg Over.Hom.left (hcq.symm.trans H)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.FiberHilbertFamily
