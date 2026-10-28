import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceProperties
import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ConeProperties

/-! # Space Chart Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpaceChartBaseChange.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: an actual open-chart condition for affine-space bundles -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

/-- Every point has an open base neighborhood whose entire inverse image
is identified with a finite relative affine space by a cartesian square. -/
def HasAffineSpaceCharts {E X : Scheme.{0}} (p : E ⟶ X) : Prop :=
  ∀ x : X, ∃ (U : Scheme.{0}) (i : U ⟶ X) (ι : Type) (_ : Finite ι)
    (j : AffineSpace ι U ⟶ E), IsOpenImmersion i ∧ IsOpenImmersion j ∧
      x ∈ Set.range i ∧ IsPullback (AffineSpace ι U ↘ U) j i p

theorem hasAffineSpaceCharts_of_specCharts {E X : Scheme.{0}} (p : E ⟶ X)
    (h : ∀ x : X, ∃ (B : CommRingCat.{0}) (i : Spec B ⟶ X) (ι : Type) (_ : Finite ι)
      (j : AffineSpace ι (Spec B) ⟶ E), IsOpenImmersion i ∧ IsOpenImmersion j ∧
        x ∈ Set.range i ∧ IsPullback (AffineSpace ι (Spec B) ↘ Spec B) j i p) :
    HasAffineSpaceCharts p := by
  intro x
  obtain ⟨B, i, ι, hi, j, h⟩ := h x
  exact ⟨Spec B, i, ι, hi, j, h⟩

theorem morphismProperty_of_hasAffineSpaceCharts (P : MorphismProperty Scheme.{0})
    [IsZariskiLocalAtTarget P] {E X : Scheme.{0}} (p : E ⟶ X) (h : HasAffineSpaceCharts p)
    (hP : ∀ (ι : Type) [Finite ι] (U : Scheme.{0}), P (AffineSpace ι U ↘ U)) : P p := by
  choose U i ι hι j hi hj hx hsq using h
  let C : X.OpenCover := Scheme.Cover.mkOfCovers X U i (fun x => ⟨x, hx x⟩) hi
  exact Global.DeformationProperties.BundleCycles.morphismProperty_of_cover_pullbacks P p C (fun x => AffineSpace (ι x) (U x))
    j (fun x => AffineSpace (ι x) (U x) ↘ U x) hsq (fun x => @hP (ι x) (hι x) (U x))

theorem HasAffineSpaceCharts.smooth {E X : Scheme.{0}} {p : E ⟶ X} (h : HasAffineSpaceCharts p) :
    Smooth p := by
  have : IsZariskiLocalAtTarget (@Smooth.{0}) := HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact morphismProperty_of_hasAffineSpaceCharts (@Smooth) p h
    (fun ι _ U => FiniteAffine.SpaceProperties.BundleCycles.finiteAffineSpaceProjection_smooth ι U)

theorem HasAffineSpaceCharts.geometricallyIntegral {E X : Scheme.{0}} {p : E ⟶ X}
    (h : HasAffineSpaceCharts p) : GeometricallyIntegral p :=
  morphismProperty_of_hasAffineSpaceCharts (@GeometricallyIntegral) p h (fun _ _ _ => inferInstance)

theorem graphConormal_hasAffineSpaceCharts {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) :
    HasAffineSpaceCharts (Global.GraphNormalCone.BundleCycles.graphConormalProjection f) :=
  hasAffineSpaceCharts_of_specCharts _ (Graph.AffineSpaceCharts.BundleCycles.graphConormal_exists_affineSpaceChart f)

theorem graphNormalCone_hasAffineSpaceCharts {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) :
    HasAffineSpaceCharts (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (Graph.OpenAmbient.BundleCycles.graph f).ker ≫ Graph.OpenAmbient.BundleCycles.graphFirstProjection f) :=
  hasAffineSpaceCharts_of_specCharts _ (Graph.AffineSpaceCharts.BundleCycles.graphNormalCone_exists_affineSpaceChart f)

end

/-! # LineBundleCycles: actual affine-space chart squares under arbitrary scheme base change -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X Y U : Scheme.{0}} (p : E ⟶ X) (g : Y ⟶ X) (i : U ⟶ X)
    (ι : Type) (j : AffineSpace ι U ⟶ E)
    (h : IsPullback (AffineSpace ι U ↘ U) j i p)

include h in
theorem affineSpaceChartBaseChange_condition :
    (AffineSpace.map ι (pullback.snd g i) ≫ j) ≫ p =
      ((AffineSpace ι (pullback g i) ↘ pullback g i) ≫ pullback.fst g i) ≫ g := by
  rw [Category.assoc, ← h.w, ← Category.assoc, AffineSpace.map_over,
    Category.assoc, ← pullback.condition, ← Category.assoc]

def affineSpaceChartBaseChangeMap :
    AffineSpace ι (pullback g i) ⟶ pullback p g :=
  pullback.lift (AffineSpace.map ι (pullback.snd g i) ≫ j)
    ((AffineSpace ι (pullback g i) ↘ pullback g i) ≫ pullback.fst g i)
    (affineSpaceChartBaseChange_condition p g i ι j h)

theorem affineSpaceChartBaseChangeMap_fst :
    affineSpaceChartBaseChangeMap p g i ι j h ≫ pullback.fst p g =
      AffineSpace.map ι (pullback.snd g i) ≫ j := pullback.lift_fst _ _ _

theorem affineSpaceChartBaseChangeMap_snd :
    affineSpaceChartBaseChangeMap p g i ι j h ≫ pullback.snd p g =
      (AffineSpace ι (pullback g i) ↘ pullback g i) ≫ pullback.fst g i := pullback.lift_snd _ _ _

theorem affineSpaceChartBaseChange_isPullback :
    IsPullback (AffineSpace ι (pullback g i) ↘ pullback g i)
      (affineSpaceChartBaseChangeMap p g i ι j h) (pullback.fst g i) (pullback.snd p g) := by
  have hs := ((AffineSpace.isPullback_map (n := ι) (pullback.snd g i)).flip).paste_vert h
  rw [← pullback.condition] at hs
  have hs' : IsPullback (AffineSpace ι (pullback g i) ↘ pullback g i)
      (affineSpaceChartBaseChangeMap p g i ι j h ≫ pullback.fst p g)
      (pullback.fst g i ≫ g) p := by
    rw [affineSpaceChartBaseChangeMap_fst]
    exact hs
  exact hs'.of_bot (affineSpaceChartBaseChangeMap_snd p g i ι j h).symm
    (IsPullback.of_hasPullback p g).flip

instance affineSpaceChartBaseChangeMap_isOpenImmersion [IsOpenImmersion i] :
    IsOpenImmersion (affineSpaceChartBaseChangeMap p g i ι j h) :=
  MorphismProperty.of_isPullback (affineSpaceChartBaseChange_isPullback p g i ι j h) inferInstance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpaceChartBaseChange.BundleCycles
