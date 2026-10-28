import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.FamilyEvaluationData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.SectionEvaluationData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.FramedEvaluationComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionBundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CoefficientSectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionFiberCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionIsomorphismCriteria

/-! # Evaluation Basis Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.EvaluationBasisCoverage.PolarizedAbelianWithLevel

noncomputable section

/-! An actual geometrically complete family of sections evaluates on
each geometric fiber as a complete field basis, up to the units coming
from its chosen marked-fiber frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical
universe u

private theorem geometricallyComplete_id_fiber
    {S X : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) {r : ℕ}
    (s : Fin r → (Line.Bundles.structureModule X ⟶ M))
    (hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily f M s (𝟙 S))
    (K : Type u) [Field K] (q : Spec (.of K) ⟶ S) :
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      (pullback.snd f q).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst f q)).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst f q) (s i))) := by
  have h := hs K q
  change Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
    (pullback.snd f (q ≫ 𝟙 S)).appTop.hom
    ((Scheme.Modules.pullback (pullback.fst f (q ≫ 𝟙 S))).obj M)
    (fun i => Ample.LineBundles.pullbackSection (pullback.fst f (q ≫ 𝟙 S)) (s i))) at h
  rw [Category.comp_id] at h
  exact h

variable {S : Scheme.{u}} {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelFamilyEvaluationMatrix_geometric_basis
    (level : A.abelian.FullLevel n)
    (s : Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ) →
      (Line.Bundles.structureModule A.abelian.scheme.left ⟶ A.uniformFrameLineBundle.sheaf))
    (hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom A.uniformFrameLineBundle.sheaf s (𝟙 S))
    (e : ∀ i : Fin (n ^ (2 * g)),
      (A.uniformFrameLineBundle.pullback (A.fullLevelSectionAtIndex level i)).sheaf ≅ Line.Bundles.structureModule S)
    (K : Type u) [Field K] [IsAlgClosed K] (q : Spec (.of K) ⟶ S) :
    ∃ b : Module.Basis (Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)) K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (A.pullback q).abelian.scheme.hom).obj
        (A.pullback q).uniformFrameLineBundle.sheaf),
      ∃ z : Fin (n ^ (2 * g)) → Kˣ,
        (fun i k => Geometric.FrameOpenCover.fieldPointGlobalScalarMap q (A.fullLevelFamilyEvaluationMatrix level s e i k)) =
          (fun i => (z i : K) • (fun k =>
            (A.pullback q).fullLevelSectionEvaluation (level.pullback q)
              (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration i) (b k))) := by
  let B := A.pullback q
  let π := pullback.fst A.abelian.scheme.hom q
  let L := A.uniformFrameLineBundle
  let d := Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ
  let H : (L.pullback π).sheaf ≅ B.uniformFrameLineBundle.sheaf :=
    A.graphBundle.powerBaseChangeIso π d ≪≫
      (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left d).mapIso (A.graphBundle_baseChangeIso q).symm
  let t := fun k => Ample.LineBundles.pullbackSection π (s k) ≫ H.hom
  have hq : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination B.abelian.scheme.hom.appTop.hom
      (L.pullback π).sheaf (fun k => Ample.LineBundles.pullbackSection π (s k))) := by
    exact geometricallyComplete_id_fiber A.abelian.scheme.hom L.sheaf s hs K q
  have ht : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination B.abelian.scheme.hom.appTop.hom
      B.uniformFrameLineBundle.sheaf t) := by
    exact (Coefficient.SectionIsomorphismCriteria.coefficientSections_bijective_bundleIso_iff B.abelian.scheme.hom.appTop.hom
      H (fun k => Ample.LineBundles.pullbackSection π (s k))).mpr hq
  obtain ⟨b, hb⟩ := HilbertConstruction.Field.CoefficientSectionBasis.field_completeSectionFamily_has_basis B.abelian.scheme.hom
    B.uniformFrameLineBundle.sheaf t ht
  let x := A.fullLevelSectionAtIndex level
  let y := B.fullLevelSectionAtIndex (level.pullback q)
  have hy (i : Fin (n ^ (2 * g))) : y i ≫ π = q ≫ x i :=
    A.abelian.fullLevelGlobalSection_pullback level q (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration i)
  let e₀ := fun i => Family.FramedEvaluationBaseChange.familySectionFrameBaseChange L q π (x i) (y i) (hy i) (e i)
  let e₁ := fun i => Framed.SectionBundleTransport.transportedSectionFrame (y i) H (e₀ i)
  choose z hz using fun i : Fin (n ^ (2 * g)) =>
    HilbertConstruction.Field.FramedEvaluationComparison.fieldFramedSectionValue_eq_unit_mul B.uniformFrameLineBundle (y i) (e₁ i)
  have heq (i : Fin (n ^ (2 * g))) (k : Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)) :
      Geometric.FrameOpenCover.fieldPointGlobalScalarMap q (A.fullLevelFamilyEvaluationMatrix level s e i k) =
        (z i : K) * B.fullLevelSectionEvaluation (level.pullback q) (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration i) (b k) := by
    have hc : B.fullLevelSectionEvaluation (level.pullback q) (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration i) (b k) =
        Rational.LineBundleEvaluation.rationalLineBundleSectionValue B.uniformFrameLineBundle (y i) (t k) := by
      change Rational.LineBundleEvaluation.rationalLineBundleSectionValue B.uniformFrameLineBundle (y i)
        ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap B.abelian.scheme.hom)
          B.uniformFrameLineBundle.sheaf).symm (b k)) = _
      exact congrArg (Rational.LineBundleEvaluation.rationalLineBundleSectionValue B.uniformFrameLineBundle (y i)) (congrFun hb k)
    rw [hc]
    calc
      _ = Geometric.FrameOpenCover.fieldPointGlobalScalarMap (𝟙 (Spec (.of K)))
          (q.appTop (Family.FramedSectionEvaluation.familyFramedSectionValue L (x i) (e i) (s k))) := by
        simp only [Geometric.FrameOpenCover.fieldPointGlobalScalarMap, Scheme.Hom.id_appTop, RingHom.comp_apply]
        rfl
      _ = Geometric.FrameOpenCover.fieldPointGlobalScalarMap (𝟙 (Spec (.of K)))
          (Family.FramedSectionEvaluation.familyFramedSectionValue (L.pullback π) (y i) (e₀ i) (Ample.LineBundles.pullbackSection π (s k))) :=
        congrArg (Geometric.FrameOpenCover.fieldPointGlobalScalarMap (𝟙 (Spec (.of K))))
          (Family.FramedEvaluationBaseChange.familyFramedSectionValue_baseChange L q π (x i) (y i) (hy i) (e i) (s k)).symm
      _ = Geometric.FrameOpenCover.fieldPointGlobalScalarMap (𝟙 (Spec (.of K)))
          (Family.FramedSectionEvaluation.familyFramedSectionValue B.uniformFrameLineBundle (y i) (e₁ i) (t k)) :=
        congrArg (Geometric.FrameOpenCover.fieldPointGlobalScalarMap (𝟙 (Spec (.of K))))
          (Framed.SectionBundleTransport.familyFramedSectionValue_bundleIso (y i) H (e₀ i) (Ample.LineBundles.pullbackSection π (s k))).symm
      _ = _ := hz i (t k)
  have hfun : (fun i k => Geometric.FrameOpenCover.fieldPointGlobalScalarMap q
        (A.fullLevelFamilyEvaluationMatrix level s e i k)) =
      (fun i => (z i : K) • (fun k => B.fullLevelSectionEvaluation (level.pullback q)
        (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration i) (b k))) := by
    funext i k
    exact heq i k
  exact ⟨b, z, hfun⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.EvaluationBasisCoverage.PolarizedAbelianWithLevel
