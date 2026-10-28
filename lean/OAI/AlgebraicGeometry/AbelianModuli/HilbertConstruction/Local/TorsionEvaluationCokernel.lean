import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EvenGraphEvaluationRetraction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FramedGraphSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.PolynomialTwistingSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SourceBundleFramedEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.PolynomialEvaluationComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ConfigurationEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.RowLinearEquivalence

/-! # Torsion Evaluation Cokernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TorsionEvaluationCokernel

noncomputable section

/-! Over a noetherian local ring, the polynomial evaluation map of a
normalized high-torsion configuration has projective cokernel. The
proof constructs its factorization through actual graph-power sections,
including the unit changes between polynomial and fiber coordinates. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {g N n r : ℕ} {δ : Fin g → ℕ} [NeZero n] {P : Polynomial ℚ}

theorem localAuxiliaryTorsionEvaluation_projective_cokernel
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
    (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R r P)
    (e : A.abelian.scheme ≅ HilbertConstruction.Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
    (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback e.hom.left).sheaf ≅
      (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)
    (hg : 0 < g) (hδ : ∀ j, 0 < δ j) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (level : A.abelian.FullLevel n) (D : ℕ) (hD : 0 < D)
    (hdegree : HilbertScheme.Presentations.RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} r P ≤ D)
    (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < n ^ 2)
    (w : Multiplicative (Fin (2 * g) → ZMod n) → Fin (r + 1) → R)
    (i : Multiplicative (Fin (2 * g) → ZMod n) → Fin (r + 1)) (hi : ∀ c, w c (i c) = 1)
    (hw : ∀ c, (A.abelian.fullLevelGlobalSection level c ≫ e.hom.left) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R (w c) (i c) (hi c)) :
    Module.Projective R ((Multiplicative (Fin (2 * g) → ZMod n) → R) ⧸
      (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D).range) := by
  have : IsNoetherianRing Γ(Spec (.of R), ⊤) := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
  let t := Graph.EmbeddingNumerics.graphSquareSectionRank g δ * D
  have ht : 0 < t := Nat.mul_pos (Graph.EmbeddingNumerics.graphSquareSectionRank_pos g δ hδ) hD
  have htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t := by
    simpa only [t, Nat.mul_one] using
      Nat.mul_le_mul_left (Graph.EmbeddingNumerics.graphSquareSectionRank g δ) (Nat.succ_le_of_lt hD)
  have hbound : EvenGraphTorsionBound.evenGraphTorsionDegree g δ t < n ^ 2 :=
    (Bounded.GraphTorsionSectionDetection.evenGraphTorsionDegree_mono g δ
      (Nat.mul_le_mul_left (Graph.EmbeddingNumerics.graphSquareSectionRank g δ) (Nat.le_max_right 1 D))).trans_lt hlarge
  let L := ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal D
  let M := A.graphBundle.tensorPower (2 * t)
  let H : (L.pullback e.hom.left).sheaf ≅ M.sheaf := Affine.EmbeddedTorsionDetection.embeddedGraphTwistingPowerIsoOverRing A I.ideal e eL D
  let x := A.abelian.fullLevelGlobalSection level
  let y := fun c => x c ≫ e.hom.left
  have hy (c : Multiplicative (Fin (2 * g) → ZMod n)) :
      y c ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I.ideal) = 𝟙 _ := by
    change (x c ≫ e.hom.left) ≫ (HilbertConstruction.Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom = _
    rw [Category.assoc, e.hom.w]
    exact A.abelian.fullLevelGlobalSection_comp level c
  let fI := fun c => SpectrumLineBundleFrames.localSpectrumLineBundleIso (L.pullback (y c))
  let fG := fun c => SourceBundleFramedEvaluation.sourceBundleSectionFrame L M (x c) e.hom.left H (fI c)
  obtain ⟨B₀⟩ := A.local_exists_completeFramedEvenGraphSections hN hunit level t ht
  let B : A.CompleteFramedEvenGraphSections level t := { B₀ with frames := fG }
  let F := A.fullLevelAffineEvenGraphEvaluation level t B.frames
  obtain ⟨q, hq⟩ := A.completeFramedEvenGraphEvaluation_leftInverse hg hδ hN hunit
    level t ht htlarge hbound B
  let E := IsoSchemeSectionEquiv.sourceBundleIsoSchemeSectionEquiv e L.sheaf H
  let C := E.toLinearMap.comp (SaturatedPolynomialSectionMap.homogeneousPolynomialTwistingSectionMap I.ideal D)
  have hC : Function.Surjective C := E.surjective.comp
    (Uniform.PolynomialTwistingSections.homogeneousPolynomialTwistingSectionMap_surjective_uniform I.ideal P I.hilbert D hdegree)
  have hrow (c : Multiplicative (Fin (2 * g) → ZMod n)) (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R r D) :
      F (C p) c = Framed.PolynomialEvaluationComparison.framedHomogeneousPolynomialEvaluation I.ideal D (y c) (hy c) (fI c) p := by
    have h := LinearMap.congr_fun (SourceBundleFramedEvaluation.affineFramedSectionEvaluation_sourceBundleIso e L M (x c)
      (A.abelian.fullLevelGlobalSection_comp level c) H (fI c) (hy c))
      (SaturatedPolynomialSectionMap.homogeneousPolynomialTwistingSectionMap I.ideal D p)
    exact h
  choose a ha using fun c : Multiplicative (Fin (2 * g) → ZMod n) =>
    Framed.PolynomialEvaluationComparison.framedPolynomialEvaluation_eq_unit_mul I.ideal D (y c) (hy c) (fI c) hD (w c) (i c) (hi c) (hw c)
  let u := Unit.RowLinearEquivalence.unitRowLinearEquiv a
  have hfactor : F.comp C = u.toLinearMap.comp (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D) := by
    apply LinearMap.ext
    intro p
    funext c
    change F (C p) c = (a c : R) * MvPolynomial.eval₂Hom (algebraMap R R) (w c) p.val
    rw [hrow]
    exact ha c p
  have heval : Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D = u.symm.toLinearMap.comp (F.comp C) := by
    apply LinearMap.ext
    intro p
    have h := LinearMap.congr_fun hfactor p
    change F (C p) = u (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D p) at h
    change Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D p = u.symm (F (C p))
    rw [h, u.symm_apply_apply]
  rw [heval]
  exact Unit.RowLinearEquivalence.projective_cokernel_of_rescaled_split_factorization u.symm F q hq C hC

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TorsionEvaluationCokernel
