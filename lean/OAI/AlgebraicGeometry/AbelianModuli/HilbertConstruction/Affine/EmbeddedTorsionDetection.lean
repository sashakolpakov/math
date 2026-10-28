import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.ConfigurationDeterminesIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TensorPowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ProjectiveFamilies

/-! # Embedded Torsion Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A complete graph-power basis with actual torsion fiber frames
gives detection of twisting sections in a homogeneous presentation,
over an arbitrary affine ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
variable {R : Type u} [CommRing R] {g N n r : ℕ} {δ : Fin g → ℕ}

section
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))

structure PolarizationData.PolarizedAbelianWithFullLevel.CompleteFramedEvenGraphSections (level : A.abelian.FullLevel n) (t : ℕ) where
  rank : ℕ
  basis : Module.Basis (Fin rank) R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
    (A.graphBundle.tensorPower (2 * t)).sheaf)
  geometricComplete : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom
    (A.graphBundle.tensorPower (2 * t)).sheaf
    (Coefficient.RingSectionBasis.coefficientRingBasisFamily (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom)
      (A.graphBundle.tensorPower (2 * t)).sheaf basis) (𝟙 (Spec (.of R)))
  frames : ∀ c : Multiplicative (Fin (2 * g) → ZMod n),
    ((A.graphBundle.tensorPower (2 * t)).pullback (A.abelian.fullLevelGlobalSection level c)).sheaf ≅
      Line.Bundles.structureModule (Spec (.of R))

theorem PolarizationData.PolarizedAbelianWithFullLevel.CompleteFramedEvenGraphSections.detects [NeZero n]
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (level : A.abelian.FullLevel n) (t : ℕ) (ht : 0 < t)
    (htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t)
    (hlarge : EvenGraphTorsionBound.evenGraphTorsionDegree g δ t < n ^ 2)
    (B : A.CompleteFramedEvenGraphSections level t) :
    Section.DetectionByFamilies.SectionsDetectedBy (A.graphBundle.tensorPower (2 * t)) (A.abelian.fullLevelGlobalSection level) :=
  A.evenGraphPower_sectionsDetectedBy_fullLevel hg hδ hN hunit level t ht htlarge hlarge
    B.basis B.geometricComplete B.frames

end

variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R r))
variable (e : A.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I)
variable (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).pullback e.hom.left).sheaf ≅
  (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)

def Affine.EmbeddedTorsionDetection.embeddedGraphTwistingPowerIsoOverRing (d : ℕ) :
    ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).pullback e.hom.left).sheaf ≅
      (A.graphBundle.tensorPower (2 * (Graph.EmbeddingNumerics.graphSquareSectionRank g δ * d))).sheaf :=
  (Scheme.Modules.pullback e.hom.left).mapIso (ProjectiveTwisting.TensorPowers.projectiveTwistingBundle_tensorPowerIso I d).symm ≪≫
    (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).powerBaseChangeIso e.hom.left d ≪≫
    (TensorPower.Maps.tensorPowerFunctor A.abelian.scheme.left d).mapIso eL ≪≫
    (A.graphBundle.tensorPowerComposeIso d (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).symm ≪≫
    eqToIso (congrArg (fun k => (A.graphBundle.tensorPower k).sheaf)
      (show d * (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ) = 2 * (Graph.EmbeddingNumerics.graphSquareSectionRank g δ * d) by ring))

include eL in
theorem Affine.EmbeddedTorsionDetection.affineEmbeddedGraph_sectionsDetectedBy_fullLevel [NeZero n]
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (level : A.abelian.FullLevel n) (D : ℕ) (d : ℕ) (hd : 0 < d) (hdD : d ≤ D)
    (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < n ^ 2)
    (B : A.CompleteFramedEvenGraphSections level (Graph.EmbeddingNumerics.graphSquareSectionRank g δ * d)) :
    Section.DetectionByFamilies.SectionsDetectedBy (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d)
      (fun c => A.abelian.fullLevelGlobalSection level c ≫ e.hom.left) := by
  have ht : 0 < Graph.EmbeddingNumerics.graphSquareSectionRank g δ * d :=
    Nat.mul_pos (Graph.EmbeddingNumerics.graphSquareSectionRank_pos g δ hδ) hd
  have htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ Graph.EmbeddingNumerics.graphSquareSectionRank g δ * d := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (Graph.EmbeddingNumerics.graphSquareSectionRank g δ) (Nat.succ_le_of_lt hd)
  have hb : EvenGraphTorsionBound.evenGraphTorsionDegree g δ (Graph.EmbeddingNumerics.graphSquareSectionRank g δ * d) < n ^ 2 :=
    (Bounded.GraphTorsionSectionDetection.evenGraphTorsionDegree_mono g δ
      (Nat.mul_le_mul_left (Graph.EmbeddingNumerics.graphSquareSectionRank g δ) (hdD.trans (Nat.le_max_right 1 D)))).trans_lt hlarge
  exact Section.DetectionByFamilies.SectionsDetectedBy.of_schemeIso (A.abelian.fullLevelGlobalSection level)
    (PolarizationData.PolarizedAbelianWithFullLevel.CompleteFramedEvenGraphSections.detects
      A hg hδ hN hunit level _ ht htlarge hb B)
    ((Over.forget _).mapIso e) (Affine.EmbeddedTorsionDetection.embeddedGraphTwistingPowerIsoOverRing A I e eL d)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
