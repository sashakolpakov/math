import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionMorphism
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Embedding

noncomputable section

/-!
An explicit closed-immersion criterion for the section morphisms constructed
for HilbertConstruction. Surjectivity is required of the actual section-ratio chart maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X : Scheme.{u}} {L : X.Modules} {n : ℕ}

private theorem standardChart_openImmersion (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) :
    IsOpenImmersion (Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one) := by
  change IsOpenImmersion ((Proj.basicOpenIsoSpec (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one).inv ≫
    (Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)).ι)
  infer_instance

/-- The map from a section's nonvanishing open to its affine projective chart. -/
def sectionAffineChart (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L)) (i : Fin (n + 1)) :
    (Ample.LineBundles.sectionNonvanishing (s i)).toScheme ⟶ Spec (.of (ProjectiveChart.Evaluation.projectiveChartRing Γ(S, ⊤) n i)) :=
  (Ample.LineBundles.sectionNonvanishing (s i)).toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (ProjectiveChart.Evaluation.projectiveChartEvaluation ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
      (fun k => Frames.sectionRatio (s i) (s k)) i (Frames.sectionRatio_self (s i))))

theorem sectionAffineChart_away (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L)) (i : Fin (n + 1)) :
    sectionAffineChart f s i ≫ Proj.awayι (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X Γ(S, ⊤) i) Nat.zero_lt_one = ChartOverlaps.sectionAbsoluteChart f s i := rfl

/-- The affine chart square is a pullback, using the computed chart preimage. -/
theorem sectionAffineChart_isPullback (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) (i : Fin (n + 1)) :
    IsPullback (sectionAffineChart f s i) (Ample.LineBundles.sectionNonvanishing (s i)).ι
      (Proj.awayι (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X Γ(S, ⊤) i) Nat.zero_lt_one)
      (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) := by
  have := standardChart_openImmersion Γ(S, ⊤) n i
  apply IsOpenImmersion.isPullback
  · exact (SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict f s hs i).trans (sectionAffineChart_away f s i).symm
  · exact (congrArg (fun U : (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left.Opens =>
        SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ⁻¹ᵁ U)
      (Proj.opensRange_awayι (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X Γ(S, ⊤) i) Nat.zero_lt_one)).trans
      ((ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage f s hs i).trans
        (Ample.LineBundles.sectionNonvanishing (s i)).opensRange_ι.symm)

/-- The affine spectra of the standard chart rings cover projective space. -/
def standardProjectiveAffineCover (R : Type u) [CommRing R] (n : ℕ) :
    Scheme.OpenCover.{0} (Projective.ProjectivePresentations.affineProjectiveSpace R n).left where
  I₀ := Fin (n + 1)
  X i := Spec (.of (ProjectiveChart.Evaluation.projectiveChartRing R n i))
  f i := Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun i => standardChart_openImmersion R n i⟩
    obtain ⟨i, hi⟩ := StandardProjectiveCharts.standardProjectiveCharts_cover R n x
    have := standardChart_openImmersion R n i
    refine ⟨i, ?_⟩
    change x ∈ (Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one).opensRange
    exact (congrArg (fun U : (Projective.ProjectivePresentations.affineProjectiveSpace R n).left.Opens => x ∈ U)
      (Proj.opensRange_awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one)).to_iff.mpr hi

/-- Surjective chart evaluations make the section morphism a closed immersion. -/
theorem sectionAbsoluteMorphism_closedImmersion (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)))
    (hgen : ∀ i, Function.Surjective
      (ProjectiveChart.Evaluation.projectiveChartEvaluation ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
        (fun k => Frames.sectionRatio (s i) (s k)) i (Frames.sectionRatio_self (s i)))) :
    IsClosedImmersion (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (standardProjectiveAffineCover Γ(S, ⊤) n)
  intro i
  have : IsAffine (Ample.LineBundles.sectionNonvanishing (s i)).toScheme := ha i
  have hspec : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (ProjectiveChart.Evaluation.projectiveChartEvaluation ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
        (fun k => Frames.sectionRatio (s i) (s k)) i (Frames.sectionRatio_self (s i))))) :=
    IsClosedImmersion.spec_of_surjective _ (hgen i)
  have hto : IsClosedImmersion (Ample.LineBundles.sectionNonvanishing (s i)).toScheme.toSpecΓ := by
    infer_instance
  have hchart : IsClosedImmersion (sectionAffineChart f s i) :=
    @IsClosedImmersion.comp _ _ _ _ _ hto hspec
  let h := (sectionAffineChart_isPullback f s hs i).flip
  have hh : IsClosedImmersion (h.isoPullback.inv ≫ sectionAffineChart f s i) :=
    @IsClosedImmersion.comp _ _ _ _ _ inferInstance hchart
  have he : h.isoPullback.inv ≫ sectionAffineChart f s i =
      (standardProjectiveAffineCover Γ(S, ⊤) n).pullbackHom (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) i :=
    h.isoPullback_inv_snd
  exact he ▸ hh

/-- Over an affine base the same criterion gives a closed immersion into
relative projective space. -/
theorem sectionProjectiveMorphism_closedImmersion (f : X ⟶ S) [IsAffine S]
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)))
    (hgen : ∀ i, Function.Surjective
      (ProjectiveChart.Evaluation.projectiveChartEvaluation ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
        (fun k => Frames.sectionRatio (s i) (s k)) i (Frames.sectionRatio_self (s i)))) :
    IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left := by
  let p : (Projective.ProjectivePresentations.projectiveSpaceOver S n).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left :=
    pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have hp : (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left ≫ p = SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs :=
    pullback.lift_fst _ _ _
  have : IsClosedImmersion ((SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left ≫ p) :=
    hp.symm ▸ sectionAbsoluteMorphism_closedImmersion f s hs ha hgen
  have : IsIso p := inferInstanceAs
    (IsIso (pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ))
  exact IsClosedImmersion.of_comp _ p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Embedding
