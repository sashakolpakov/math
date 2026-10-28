import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPresentationCompleteness

/-! # Graph Power Presentation Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.GraphPowerPresentationCompleteness.StableHilbertCoverage

noncomputable section

/-! A marked projective presentation of any positive graph power is
complete when its dimension equals the actual graph-power section rank. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped BigOperators
universe u

theorem canonicalPositiveGraphPowerPresentation_field_rank
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme) (d : ℕ) (hd : 0 < d)
    (h : Line.Bundles.LineBundle.classOf (A.abelian.zeroNormalizedBundle P.ampleLineBundle) =
      Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower d))
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
      P.ampleLineBundle.sheaf) = (2 : ℕ) ^ g * (∏ i, δ i) * d ^ g := by
  exact (StableHilbert.NormalizedClassCompleteness.StableHilbertCoverage.normalizedLineBundle_sections_finrank_eq A.abelian P.ampleLineBundle
    (A.graphBundle.tensorPower d) h).trans
    (A.graphBundle_positivePower_sections_finrank_normalized hg hN hNk d hd)

theorem canonicalPositiveGraphPowerPresentation_geometricallyComplete
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme) (d : ℕ) (hd : 0 < d)
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod N))
    (hσ : ∀ i, Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 S)) A.abelian A.level P (σ i) =
      Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint S P.dimension i)
    (h : Line.Bundles.LineBundle.classOf (A.abelian.zeroNormalizedBundle P.ampleLineBundle) =
      Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower d))
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (hn : P.dimension + 1 = (2 : ℕ) ^ g * (∏ i, δ i) * d ^ g) :
    ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom P.ampleLineBundle.sheaf
      P.canonicalSectionData.sections (𝟙 S) := by
  apply StableHilbert.PresentationCompleteness.StableHilbertCoverage.canonicalSections_geometricallyComplete_of_markedFrame_rank A.abelian A.level P σ hσ
  intro K _ f
  exact (canonicalPositiveGraphPowerPresentation_field_rank (A.pullback f)
    (P.baseChange f) d hd (StableHilbert.NormalizedClassCompleteness.StableHilbertCoverage.normalizedGraphPowerClass_baseChange A P h f) hg hN
    (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit f)).trans hn.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.GraphPowerPresentationCompleteness.StableHilbertCoverage
