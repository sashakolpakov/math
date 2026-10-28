import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpaceChartBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen

/-! # Source Base -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Divisors.LineBundles

/-! Relative affine-space charts may cover the source without exhausting
the whole inverse image of a base open. This includes projective-space charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def AffineSpace.SourceBase.BundleCycles.HasAffineSpaceSourceCharts {E X : Scheme.{0}} (p : E ⟶ X) : Prop :=
  ∀ z : E, ∃ (U : Scheme.{0}) (i : U ⟶ X) (ι : Type) (_ : Finite ι)
    (j : AffineSpace ι U ⟶ E), IsOpenImmersion i ∧ IsOpenImmersion j ∧
      z ∈ Set.range j ∧ (AffineSpace ι U ↘ U) ≫ i = j ≫ p

theorem Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts.sourceCharts {E X : Scheme.{0}} {p : E ⟶ X}
    (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p) : LineBundles.AffineSpace.SourceBase.BundleCycles.HasAffineSpaceSourceCharts p := by
  intro z
  obtain ⟨U, i, ι, hι, j, hi, hj, hx, hs⟩ := h (p z)
  obtain ⟨u, hu⟩ := hx
  obtain ⟨a, _, hja⟩ := Scheme.exists_preimage_of_isPullback hs u z hu
  exact ⟨U, i, ι, hι, j, hi, hj, ⟨a, hja⟩, hs.w⟩

theorem AffineSpace.SourceBase.BundleCycles.HasAffineSpaceSourceCharts.smooth {E X : Scheme.{0}} {p : E ⟶ X}
    (h : LineBundles.AffineSpace.SourceBase.BundleCycles.HasAffineSpaceSourceCharts p) : Smooth p := by
  choose U i ι hι j hi hj hx hs using h
  let C : E.OpenCover := Scheme.Cover.mkOfCovers E (fun z => AffineSpace (ι z) (U z)) j
    (fun z => ⟨z, hx z⟩) hj
  have : IsZariskiLocalAtSource (@Smooth.{0}) := HasRingHomProperty.instIsZariskiLocalAtSource
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) C
  intro z
  let := hι z
  let := hi z
  change Smooth (j z ≫ p)
  rw [← hs z]
  let := FiniteAffine.SpaceProperties.BundleCycles.finiteAffineSpaceProjection_smooth (ι z) (U z)
  infer_instance

end AlgebraicGeometry.Divisors.LineBundles

namespace AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceBase.BundleCycles
open _root_.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
section

/-! # LineBundleCycles: actual source affine-space charts under arbitrary scheme base change -/

variable {E X Y U : Scheme.{0}} (p : E ⟶ X) (g : Y ⟶ X) (i : U ⟶ X)
    (ι : Type) (j : AffineSpace ι U ⟶ E)
    (h : (AffineSpace ι U ↘ U) ≫ i = j ≫ p)

include h in
theorem affineSpaceSourceBaseChange_condition :
    (AffineSpace.map ι (pullback.snd g i) ≫ j) ≫ p =
      ((AffineSpace ι (pullback g i) ↘ pullback g i) ≫ pullback.fst g i) ≫ g := by
  rw [Category.assoc, ← h, ← Category.assoc, AffineSpace.map_over,
    Category.assoc, ← pullback.condition, ← Category.assoc]

def affineSpaceSourceBaseChangeMap :
    AffineSpace ι (pullback g i) ⟶ pullback p g :=
  pullback.lift (AffineSpace.map ι (pullback.snd g i) ≫ j)
    ((AffineSpace ι (pullback g i) ↘ pullback g i) ≫ pullback.fst g i)
    (affineSpaceSourceBaseChange_condition p g i ι j h)

theorem affineSpaceSourceBaseChangeMap_fst :
    affineSpaceSourceBaseChangeMap p g i ι j h ≫ pullback.fst p g =
      AffineSpace.map ι (pullback.snd g i) ≫ j := pullback.lift_fst _ _ _

theorem affineSpaceSourceBaseChangeMap_snd :
    affineSpaceSourceBaseChangeMap p g i ι j h ≫ pullback.snd p g =
      (AffineSpace ι (pullback g i) ↘ pullback g i) ≫ pullback.fst g i := pullback.lift_snd _ _ _

theorem affineSpaceSourceBaseChange_isPullback :
    IsPullback (affineSpaceSourceBaseChangeMap p g i ι j h)
      (AffineSpace.map ι (pullback.snd g i)) (pullback.fst p g) j := by
  have hs := (AffineSpace.isPullback_map (n := ι) (pullback.snd g i)).paste_vert
    (IsPullback.of_hasPullback g i).flip
  rw [h] at hs
  have hs' : IsPullback
      (AffineSpace.map ι (pullback.snd g i))
      (affineSpaceSourceBaseChangeMap p g i ι j h ≫ pullback.snd p g) (j ≫ p) g := by
    rw [affineSpaceSourceBaseChangeMap_snd]
    exact hs
  exact hs'.flip.of_right (affineSpaceSourceBaseChangeMap_fst p g i ι j h)
    (IsPullback.of_hasPullback p g).flip

instance affineSpaceSourceBaseChangeMap_isOpenImmersion [IsOpenImmersion j] :
    IsOpenImmersion (affineSpaceSourceBaseChangeMap p g i ι j h) :=
  MorphismProperty.of_isPullback (affineSpaceSourceBaseChange_isPullback p g i ι j h).flip inferInstance

end

/-! An affine-space open over the entire base remains an actual
affine-space open after arbitrary base change. -/

variable {E X Y : Scheme.{0}} (p : E ⟶ X) (ι : Type)
    (j : AffineSpace ι X ⟶ E) (hj : j ≫ p = (AffineSpace ι X ↘ X)) (b : Y ⟶ X)

def affineSpaceRelativeBaseChangeMap : AffineSpace ι Y ⟶ pullback p b :=
  pullback.lift (AffineSpace.map ι b ≫ j) (AffineSpace ι Y ↘ Y)
    (by rw [Category.assoc, hj, AffineSpace.map_over])

theorem affineSpaceRelativeBaseChangeMap_fst :
    affineSpaceRelativeBaseChangeMap p ι j hj b ≫ pullback.fst p b = AffineSpace.map ι b ≫ j :=
  pullback.lift_fst _ _ _

theorem affineSpaceRelativeBaseChangeMap_snd :
    affineSpaceRelativeBaseChangeMap p ι j hj b ≫ pullback.snd p b = (AffineSpace ι Y ↘ Y) :=
  pullback.lift_snd _ _ _

theorem affineSpaceRelativeBaseChangeMap_isPullback :
    IsPullback (affineSpaceRelativeBaseChangeMap p ι j hj b) (AffineSpace.map ι b) (pullback.fst p b) j := by
  have H : IsPullback (affineSpaceRelativeBaseChangeMap p ι j hj b ≫ pullback.snd p b)
      (AffineSpace.map ι b) b (j ≫ p) := by
    rw [affineSpaceRelativeBaseChangeMap_snd, hj]
    exact (AffineSpace.isPullback_map (n := ι) b).flip
  exact H.of_right (affineSpaceRelativeBaseChangeMap_fst p ι j hj b) (IsPullback.of_hasPullback p b).flip

instance affineSpaceRelativeBaseChangeMap_isOpenImmersion [IsOpenImmersion j] :
    IsOpenImmersion (affineSpaceRelativeBaseChangeMap p ι j hj b) :=
  MorphismProperty.of_isPullback (affineSpaceRelativeBaseChangeMap_isPullback p ι j hj b).flip inferInstance

end AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceBase.BundleCycles

end

end OAI
