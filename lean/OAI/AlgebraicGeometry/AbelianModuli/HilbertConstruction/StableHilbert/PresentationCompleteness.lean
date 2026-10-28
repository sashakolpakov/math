import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.CanonicalCompleteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.HomogeneousCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ScalarCoordinateCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoSchemeSectionEquiv
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpecIsoProjections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CoordinateProjectiveBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionEquations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartProjectivePoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionFiberCriterion

/-! # Presentation Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PresentationCompleteness

noncomputable section

/-! The standard frame detects the actual canonical coordinate
sections of any flat projective presentation over a field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
namespace StableHilbertCoverage

theorem affineProjectiveChartMap_identity_eq_specIso_inv
    (R : CommRingCat.{u}) (n : ℕ) :
    AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec R)) n = (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso R n).inv.left := by
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback (Spec R) n).hom_ext
  · have hc : AffineProjective.Charts.affinePointCoefficients (𝟙 (Spec R)) = (Scheme.ΓSpecIso R).hom := by
      simp only [AffineProjective.Charts.affinePointCoefficients, Scheme.Hom.id_appTop, Category.id_comp]
    exact (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_affine (𝟙 (Spec R)) n).trans
      ((congrArg (fun c => Projective.CoefficientFunctoriality.polynomialProjectiveMap c n) hc).trans
        (Projective.SpecIsoProjections.projectiveSpaceOverSpecIso_inv_coefficients R n).symm)
  · exact (AffineProjective.Charts.affineProjectiveChartMap_over (𝟙 (Spec R)) n).trans
      ((Category.comp_id _).trans (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso R n).inv.w.symm)

private theorem affineCoordinates_congr
    (R : Type u) [CommRing R] {n : ℕ} (v w : Fin (n + 1) → R)
    (i : Fin (n + 1)) (hv : v i = 1) (hw : w i = 1) (h : v = w) :
    AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R v i hv =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R w i hw := by
  subst w
  rfl

theorem standardBasisProjectivePoint_affine
    (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint (Spec (.of R)) n i).left =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R (Pi.single i 1) i (Pi.single_eq_same i 1) ≫
        AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of R))) n := by
  classical
  let v := Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates (Spec (.of R)) n i
  have hi : v i = 1 := ite_eq_left rfl
  have hv : (fun k => (Scheme.ΓSpecIso (.of R)).hom (v k)) = Pi.single i 1 := by
    funext k
    by_cases h : i = k
    · subst k
      simp only [v, Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates, ite_true, map_one, Pi.single_eq_same]
    · simp only [v, Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates, ite_eq_right h, map_zero,
        Pi.single_eq_of_ne (Ne.symm h)]
  exact (ScalarCoordinateCoverage.StableHilbertCoverage.scalarCoordinateProjectivePoint_affine R v
    (Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates_cover (Spec (.of R)) n i) i hi).trans
      (congrArg (fun p => p ≫ AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of R))) n)
        (affineCoordinates_congr R _ _ i _ _ hv))

private theorem point_of_embedding_square
    {C : Type*} [Category* C] {T X Y P Q : C}
    (x : T ⟶ X) (e : X ⟶ Y) (j : Y ⟶ P) (q : P ⟶ Q) [hmono : Mono q]
    (p : T ⟶ P) (i : X ⟶ Q)
    (he : (e ≫ j) ≫ q = i) (hx : x ≫ i = p ≫ q) : (x ≫ e) ≫ j = p := by
  apply (cancel_mono q).mp
  exact ((congrArg (fun a => a ≫ q) (Category.assoc x e j)).trans
    (Category.assoc x (e ≫ j) q)).trans
      ((congrArg (fun a => x ≫ a) he).trans hx)

private theorem model_standardFrame
    {K : Type u} [Field K] {X : Over (Spec (.of K))}
    (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K P.dimension))
    (e : X ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I)
    (he : (e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of K))) P.dimension = P.embedding.left)
    (x : Fin (P.dimension + 1) → (Over.mk (𝟙 (Spec (.of K))) ⟶ X))
    (hx : ∀ i, x i ≫ P.embedding = Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint (Spec (.of K)) P.dimension i) :
    ∀ i, ((x i).left ≫ e.hom.left) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of K) K (Pi.single i 1) i (Pi.single_eq_same i 1) := by
  let q := AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of K))) P.dimension
  let hq : IsIso q :=
    (AffineProjective.Charts.affineProjectiveChartMap_isPullback (𝟙 (Spec (.of K))) P.dimension).isIso_fst_of_isIso
  let hmono : Mono q := @IsIso.mono_of_iso _ _ _ _ q hq
  intro i
  exact point_of_embedding_square (C := Scheme.{u}) (x i).left e.hom.left
    (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) q (hmono := hmono)
    (AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of K) K (Pi.single i 1) i (Pi.single_eq_same i 1))
    P.embedding.left he ((congrArg Over.Hom.left (hx i)).trans
      (standardBasisProjectivePoint_affine K P.dimension i))

private theorem model_linearSections_bijective
    {K : Type u} [Field K] {X : Over (Spec (.of K))}
    (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K P.dimension))
    (e : X ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I)
    (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).pullback e.hom.left).sheaf ≅ P.ampleLineBundle.sheaf)
    (y : Fin (P.dimension + 1) → (Spec (.of K) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
    (hy : ∀ i, y i ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of K) K (Pi.single i 1) i (Pi.single_eq_same i 1))
    [Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj P.ampleLineBundle.sheaf)]
    (hr : Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj P.ampleLineBundle.sheaf) =
      P.dimension + 1) : Function.Bijective (SaturatedPolynomialSectionMap.homogeneousPolynomialTwistingSectionMap I 1) := by
  let H : ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf) ≃ₗ[K]
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj P.ampleLineBundle.sheaf) :=
    IsoSchemeSectionEquiv.sourceBundleIsoSchemeSectionEquiv e (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf eL
  let : Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf) := Module.Finite.equiv H.symm
  exact FieldCompleteness.StableHilbertCoverage.linearSections_bijective_of_frame_rank I y hy (H.finrank_eq.trans hr)

private theorem model_embedding_eq
    {K : Type u} [Field K] {X : Over (Spec (.of K))}
    (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K P.dimension))
    (e : X ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I)
    (he : (e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of K))) P.dimension = P.embedding.left) :
    e.hom ≫ (Affine.CoordinateSectionData.quotientCoordinatePresentation I).embedding = P.embedding := by
  apply Over.OverMorphism.ext
  change e.hom.left ≫ (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫
    (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of K) P.dimension).inv.left) = P.embedding.left
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => (e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) ≫ z)
      (affineProjectiveChartMap_identity_eq_specIso_inv (.of K) P.dimension).symm).trans he)

private def canonicalCompleteData_of_model_frame_rank
    {K : Type u} [Field K] {X : Over (Spec (.of K))}
    (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K P.dimension))
    (e : X ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I)
    (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).pullback e.hom.left).sheaf ≅ P.ampleLineBundle.sheaf)
    (he : (e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of K))) P.dimension = P.embedding.left)
    (x : Fin (P.dimension + 1) → (Over.mk (𝟙 (Spec (.of K))) ⟶ X))
    (hx : ∀ i, x i ≫ P.embedding = Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint (Spec (.of K)) P.dimension i)
    [Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj P.ampleLineBundle.sheaf)]
    (hr : Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj P.ampleLineBundle.sheaf) =
      P.dimension + 1) : P.canonicalSectionData.CompleteData := by
  let y := fun i => (x i).left ≫ e.hom.left
  have hI := model_linearSections_bijective P I e eL y (model_standardFrame P I e he x hx) hr
  let Q := Affine.CoordinateSectionData.quotientCoordinatePresentation I
  have heQ := model_embedding_eq P I e he
  have he' : e.inv ≫ P.embedding = Q.embedding :=
    (congrArg (fun z => e.inv ≫ z) heQ).symm.trans (e.inv_hom_id_assoc Q.embedding)
  exact CanonicalCompleteness.StableHilbertCoverage.canonicalCompleteData_of_quotientIso I hI P.embedding (hi := P.closedImmersion) e.symm he'

def canonicalCompleteData_of_frame_rank
    {K : Type u} [Field K] {X : Over (Spec (.of K))}
    [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (x : Fin (P.dimension + 1) → (Over.mk (𝟙 (Spec (.of K))) ⟶ X))
    (hx : ∀ i, x i ≫ P.embedding = Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint (Spec (.of K)) P.dimension i)
    [Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj P.ampleLineBundle.sheaf)]
    (hr : Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj P.ampleLineBundle.sheaf) =
      P.dimension + 1) : P.canonicalSectionData.CompleteData := by
  let : IsClosedImmersion P.embedding.left := P.closedImmersion
  exact canonicalCompleteData_of_model_frame_rank P (HomogeneousCoverage.StableHilbertCoverage.EmbeddingModel.ideal P.embedding)
    (HomogeneousCoverage.StableHilbertCoverage.EmbeddingModel.iso P.embedding) (HomogeneousCoverage.StableHilbertCoverage.EmbeddingModel.twistingIso P.embedding)
    (HomogeneousCoverage.StableHilbertCoverage.EmbeddingModel.embedding P.embedding) x hx hr

end StableHilbertCoverage

namespace ProjectivePresentation.SectionData
variable {S : Scheme.{u}} {X : Over S} {P : Projective.ProjectivePresentations.ProjectivePresentation X}
variable {L : Line.Bundles.LineBundle X.left}

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation.SectionData.completeData_ofCanonical (D : P.SectionData L)
    (C : P.canonicalSectionData.CompleteData) : D.CompleteData := by
  let E := C.ofBundleIso D.twistingIso
  have hs : D.sections = (P.canonicalSectionData.ofBundleIso D.twistingIso).sections := by
    funext i
    exact (D.twistingIso_coordinate i).symm
  exact ⟨E.basis, hs.trans E.sections_eq⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation.SectionData.CompleteData.bijective {D : P.SectionData L} (C : D.CompleteData) :
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination X.hom.appTop.hom L.sheaf D.sections) :=
  (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_bijective_iff _ _ _).mpr ⟨C.basis, C.sections_eq.symm⟩

end ProjectivePresentation.SectionData

namespace StableHilbertCoverage

theorem standardBasisProjectivePoint_baseChange
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) (i : Fin (n + 1)) :
    Projective.SectionBaseChange.projectiveSectionBaseChange (Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint S n i) f =
      Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint T n i := by
  classical
  let v := Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates S n i
  have he : (fun k => f.appTop (v k)) = Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates T n i := by
    funext k
    by_cases h : i = k
    · simp only [v, Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates, ite_eq_left h, map_one]
    · simp only [v, Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates, ite_eq_right h, map_zero]
  have hv : ∀ x : T, ∃ k, x ∈ T.basicOpen (f.appTop (v k)) := by
    intro x
    obtain ⟨k, hk⟩ := Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates_cover T n i x
    exact ⟨k, (congrArg (fun a => x ∈ T.basicOpen a) (congrFun he k)).mpr hk⟩
  exact (Scalar.CoordinateProjectiveBaseChange.scalarCoordinateProjectivePoint_baseChange f v
    (Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates_cover S n i) hv).trans
      (Balanced.FrameChartProjectivePoints.scalarCoordinateProjectivePoint_congr hv (Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates_cover T n i) he)

private theorem fullLevelMarkedProjectivePoint_unfold
    {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 S)) A level P c =
      Over.homMk (A.fullLevelGlobalSection level c) (A.fullLevelGlobalSection_comp level c) ≫
        P.embedding := rfl

private theorem fullLevelMarkedProjectivePoint_pullback_baseMap
    {S T : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (f : T ⟶ S)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 T)) (A.pullback f) (level.pullback f)
      (P.baseChange f) c).left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f P.dimension =
        f ≫ (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 S)) A level P c).left := by
  let x := A.fullLevelGlobalSection level c
  let y := (A.pullback f).fullLevelGlobalSection (level.pullback f) c
  have hy : y ≫ pullback.fst A.scheme.hom f = f ≫ x :=
    A.fullLevelGlobalSection_pullback level f c
  have hi : (P.baseChange f).embedding.left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f P.dimension =
      pullback.fst A.scheme.hom f ≫ P.embedding.left :=
    Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding_baseMap P.embedding f
  exact (Category.assoc y _ _).trans ((congrArg (fun z => y ≫ z) hi).trans
    ((Category.assoc y _ _).symm.trans
      ((congrArg (fun z => z ≫ P.embedding.left) hy).trans (Category.assoc f x _))))

private theorem fullLevelMarkedProjectivePoint_pullback
    {S T : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (f : T ⟶ S)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 T)) (A.pullback f) (level.pullback f)
      (P.baseChange f) c =
        Projective.SectionBaseChange.projectiveSectionBaseChange (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 S)) A level P c) f := by
  apply Projective.SectionBaseChange.projectiveSections_eq_of_baseMap f
  exact (fullLevelMarkedProjectivePoint_pullback_baseMap A level P f c).trans
    (Projective.SectionBaseChange.projectiveSectionBaseChange_baseMap
      (Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 S)) A level P c) f).symm

theorem fullLevelStandardFrame_baseChange
    {S T : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod N))
    (hσ : ∀ i, Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 S)) A level P (σ i) =
      Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint S P.dimension i) (f : T ⟶ S) :
    ∀ i, Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 T)) (A.pullback f) (level.pullback f)
      (P.baseChange f) (σ i) = Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint T P.dimension i := by
  intro i
  exact (fullLevelMarkedProjectivePoint_pullback A level P f (σ i)).trans
    ((congrArg (fun p => Projective.SectionBaseChange.projectiveSectionBaseChange p f) (hσ i)).trans
      (standardBasisProjectivePoint_baseChange f P.dimension i))

private def canonicalCompleteData_of_frame_rank'
    {K : Type u} [Field K] {X : Over (Spec (.of K))}
    [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (x : Fin (P.dimension + 1) → (Over.mk (𝟙 (Spec (.of K))) ⟶ X))
    (hx : ∀ i, x i ≫ P.embedding = Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint (Spec (.of K)) P.dimension i)
    (hr : Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj P.ampleLineBundle.sheaf) =
      P.dimension + 1) : P.canonicalSectionData.CompleteData := by
  let : Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj P.ampleLineBundle.sheaf) :=
    Module.finite_of_finrank_pos (hr.symm ▸ Nat.succ_pos P.dimension)
  exact canonicalCompleteData_of_frame_rank P x hx hr

private def abelianCanonicalCompleteData_of_markedFrame_rank
    {K : Type u} [Field K] {g N : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod N))
    (hσ : ∀ i, Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 (Spec (.of K)))) A level P (σ i) =
      Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint (Spec (.of K)) P.dimension i)
    (hr : Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.scheme.hom).obj
      P.ampleLineBundle.sheaf) = P.dimension + 1) : P.canonicalSectionData.CompleteData := by
  exact canonicalCompleteData_of_frame_rank' P
    (fun i => Over.homMk (A.fullLevelGlobalSection level (σ i))
      (A.fullLevelGlobalSection_comp level (σ i)))
    (fun i => (fullLevelMarkedProjectivePoint_unfold A level P (σ i)).symm.trans (hσ i)) hr

private def pullbackCanonicalCompleteData_of_markedFrame_rank
    {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod N))
    (hσ : ∀ i, Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 S)) A level P (σ i) =
      Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint S P.dimension i)
    {K : Type u} [Field K] (f : Spec (.of K) ⟶ S)
    (hr : Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (A.pullback f).scheme.hom).obj
      (P.baseChange f).ampleLineBundle.sheaf) = P.dimension + 1) :
    (P.baseChange f).canonicalSectionData.CompleteData := by
  exact abelianCanonicalCompleteData_of_markedFrame_rank (A.pullback f) (level.pullback f)
    (P.baseChange f) σ (fullLevelStandardFrame_baseChange A level P σ hσ f) hr

private theorem canonicalSections_baseChange_bijective
    {S : Scheme.{u}} {X : Over S} (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    {K : Type u} [Field K] (f : Spec (.of K) ⟶ S)
    (C : (P.baseChange f).canonicalSectionData.CompleteData) :
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      (pullback.snd X.hom f).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst X.hom f)).obj P.ampleLineBundle.sheaf)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom f) (P.canonicalSectionData.sections i))) := by
  let E := P.canonicalSectionData.baseChange f
  exact (E.completeData_ofCanonical C).bijective

theorem canonicalSections_geometricallyComplete_of_markedFrame_rank
    {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod N))
    (hσ : ∀ i, Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 S)) A level P (σ i) =
      Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint S P.dimension i)
    (hr : ∀ (K : Type u) [Field K] (f : Spec (.of K) ⟶ S),
      Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (A.pullback f).scheme.hom).obj
        (P.baseChange f).ampleLineBundle.sheaf) = P.dimension + 1) :
    ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.scheme.hom P.ampleLineBundle.sheaf
      P.canonicalSectionData.sections (𝟙 S) := by
  intro K _ f
  change Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
    (pullback.snd A.scheme.hom (f ≫ 𝟙 S)).appTop.hom
    ((Scheme.Modules.pullback (pullback.fst A.scheme.hom (f ≫ 𝟙 S))).obj P.ampleLineBundle.sheaf)
    (fun i => Ample.LineBundles.pullbackSection (pullback.fst A.scheme.hom (f ≫ 𝟙 S))
      (P.canonicalSectionData.sections i)))
  rw [Category.comp_id]
  exact canonicalSections_baseChange_bijective P f
    (pullbackCanonicalCompleteData_of_markedFrame_rank A level P σ hσ f (hr K f))

end StableHilbertCoverage

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PresentationCompleteness
