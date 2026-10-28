import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.ProjectiveIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.MapOverBase

/-! # Projective Base Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.ProjectiveBaseCompatibility

noncomputable section

/-! The Veronese isomorphism preserves the original coefficient ring,
so it is an isomorphism over the specified base spectrum. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g] (N : ℕ) [NeZero N]

theorem veroneseAwayMap_preserves_coefficients (f : Subalgebra.veroneseSubalgebra g N) (r : R) :
    AffineChartEquivalence.veroneseAwayMap g N f (algebraMap R (HomogeneousLocalization.Away (Grading.veroneseGrading g N) f) r) =
      algebraMap R (HomogeneousLocalization.Away g f.val) r := by
  rw [HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap, HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap]
  apply HomogeneousLocalization.val_injective
  rfl

private theorem chart_base_composition {C : Type*} [Category C] {U V X Y B : C}
    (a : U ⟶ X) (f : X ⟶ Y) (q : Y ⟶ B) (p : X ⟶ B)
    (c : U ⟶ V) (b : V ⟶ Y) (d : V ⟶ B) (e : U ⟶ B)
    (h : a ≫ f = c ≫ b) (hq : b ≫ q = d) (hc : c ≫ d = e) (hp : a ≫ p = e) :
    a ≫ (f ≫ q) = a ≫ p := by
  calc
    _ = (a ≫ f) ≫ q := (Category.assoc _ _ _).symm
    _ = (c ≫ b) ≫ q := congrArg (fun k => k ≫ q) h
    _ = c ≫ d := (Category.assoc _ _ _).trans (congrArg (fun k => c ≫ k) hq)
    _ = e := hc
    _ = _ := hp.symm

theorem veroneseSchemeMorphism_over_base :
    SchemeMorphism.veroneseSchemeMorphism g N ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Grading.veroneseGrading g N) = HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap g := by
  apply (ProjectiveChartCover.veroneseOriginalOpenCover g N).hom_ext
  intro j
  change ProjectiveChartCover.positiveVeroneseChartIndex g N at j
  apply (cancel_epi (Proj.basicOpenIsoSpec g j.2.val j.2.property
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) j.1.property)).inv).mp
  change Proj.awayι g j.2.val j.2.property _ ≫
      (SchemeMorphism.veroneseSchemeMorphism g N ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Grading.veroneseGrading g N)) =
    Proj.awayι g j.2.val j.2.property _ ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap g
  let f := ProjectiveChartCover.positiveVeroneseChartElement g N j
  have hc : Spec.map (CommRingCat.ofHom (AffineChartEquivalence.veroneseAwayMap g N f)) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (HomogeneousLocalization.Away (Grading.veroneseGrading g N) f))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (HomogeneousLocalization.Away g f.val))) := by
    rw [← Spec.map_comp]
    apply congrArg (fun h : R →+* HomogeneousLocalization.Away g f.val => Spec.map (CommRingCat.ofHom h))
    apply RingHom.ext
    exact veroneseAwayMap_preserves_coefficients g N f
  exact chart_base_composition _ _ _ _ _ _ _ _
    (AffineChartNaturality.veronese_awayι_comp_map g N j.1.property f j.2.property)
    (Projective.MapOverBase.projectiveStructureMap_positiveAway (Grading.veroneseGrading g N) j.1.property j.2.property)
    hc (Projective.MapOverBase.projectiveStructureMap_positiveAway g
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) j.1.property) j.2.property)

def veroneseProjectiveOverIso :
    Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap g) ≅ Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Grading.veroneseGrading g N)) :=
  Over.isoMk (ProjectiveIsomorphism.veroneseProjectiveIso g N) (veroneseSchemeMorphism_over_base g N)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.ProjectiveBaseCompatibility
