import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.FamilyEvaluationMatrix
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionSectionEvaluationInjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisEvaluationMatrices

/-! # Graph Family Evaluation Matrix -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphFamilyEvaluationMatrix.PolarizedAbelianWithLevel

noncomputable section

/-! Framed evaluation of a geometrically complete family of sections
of an even graph power is injective on every geometric fiber. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
variable {r : ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.evenGraphFamilyEvaluationMatrix (level : A.abelian.FullLevel n) (t : ℕ)
    (s : Fin r → (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower (2 * t)).sheaf))
    (e : ∀ c : Multiplicative (Fin (2 * g) → ZMod n),
      ((A.graphBundle.tensorPower (2 * t)).pullback (A.abelian.fullLevelGlobalSection level c)).sheaf ≅
        Line.Bundles.structureModule S) : Matrix (Multiplicative (Fin (2 * g) → ZMod n)) (Fin r) Γ(S, ⊤) :=
  fun c j => Family.FramedSectionEvaluation.familyFramedSectionValue (A.graphBundle.tensorPower (2 * t))
    (A.abelian.fullLevelGlobalSection level c) (e c) (s j)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.evenGraphFamilyEvaluationMatrix_geometric_injective
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (level : A.abelian.FullLevel n) (t : ℕ) (ht : 0 < t)
    (htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t)
    (hlarge : EvenGraphTorsionBound.evenGraphTorsionDegree g δ t < n ^ 2)
    (s : Fin r → (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower (2 * t)).sheaf))
    (hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom
      (A.graphBundle.tensorPower (2 * t)).sheaf s (𝟙 S))
    (e : ∀ c : Multiplicative (Fin (2 * g) → ZMod n),
      ((A.graphBundle.tensorPower (2 * t)).pullback (A.abelian.fullLevelGlobalSection level c)).sheaf ≅
        Line.Bundles.structureModule S)
    (K : Type u) [Field K] [IsAlgClosed K] (q : Spec (.of K) ⟶ S) :
    Function.Injective (Matrix.toLin' ((A.evenGraphFamilyEvaluationMatrix level t s e).map
      (Geometric.FrameOpenCover.fieldPointGlobalScalarMap q))) := by
  let B := A.pullback q
  let π := pullback.fst A.abelian.scheme.hom q
  let L := A.graphBundle.tensorPower (2 * t)
  let H : (L.pullback π).sheaf ≅ (B.graphBundle.tensorPower (2 * t)).sheaf :=
    A.graphBundle.powerBaseChangeIso π (2 * t) ≪≫
      (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left (2 * t)).mapIso (A.graphBundle_baseChangeIso q).symm
  let a := fun j => Ample.LineBundles.pullbackSection π (s j) ≫ H.hom
  have hq : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination B.abelian.scheme.hom.appTop.hom
      (L.pullback π).sheaf (fun j => Ample.LineBundles.pullbackSection π (s j))) := by
    exact geometricallyComplete_id_fiber A.abelian.scheme.hom L.sheaf s hs K q
  have ha : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination B.abelian.scheme.hom.appTop.hom
      (B.graphBundle.tensorPower (2 * t)).sheaf a) := by
    dsimp only [a]
    erw [Coefficient.SectionBundleTransport.coefficientSectionLinearCombination_postcomp]
    exact (Coefficient.SectionBundleTransport.coefficientBundleSectionEquiv B.abelian.scheme.hom.appTop.hom H).bijective.comp hq
  obtain ⟨b, hb⟩ := HilbertConstruction.Field.CoefficientSectionBasis.field_completeSectionFamily_has_basis B.abelian.scheme.hom
    (B.graphBundle.tensorPower (2 * t)).sheaf a ha
  let x := A.abelian.fullLevelGlobalSection level
  let y := B.abelian.fullLevelGlobalSection (level.pullback q)
  have hy (c : Multiplicative (Fin (2 * g) → ZMod n)) : y c ≫ π = q ≫ x c :=
    A.abelian.fullLevelGlobalSection_pullback level q c
  let e₀ := fun c => Family.FramedEvaluationBaseChange.familySectionFrameBaseChange L q π (x c) (y c) (hy c) (e c)
  let e₁ := fun c => Framed.SectionBundleTransport.transportedSectionFrame (y c) H (e₀ c)
  choose z hz using fun c : Multiplicative (Fin (2 * g) → ZMod n) =>
    HilbertConstruction.Field.FramedEvaluationComparison.fieldFramedSectionValue_eq_unit_mul (B.graphBundle.tensorPower (2 * t)) (y c) (e₁ c)
  let F := BasisEvaluationMatrices.basisEvaluationMatrix b (B.fullLevelEvenGraphEvaluation (level.pullback q) t)
  have hF : Function.Injective (Matrix.toLin' F) :=
    BasisEvaluationMatrices.basisEvaluationMatrix_injective b _
      (B.fullLevelEvenGraphEvaluation_injective hg hδ hN
        (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit q) (level.pullback q) t ht htlarge hlarge)
  have heq : (A.evenGraphFamilyEvaluationMatrix level t s e).map (Geometric.FrameOpenCover.fieldPointGlobalScalarMap q) =
      (fun c j => (z c : K) * F c j) := by
    funext c j
    have hc : F c j = Rational.LineBundleEvaluation.rationalLineBundleSectionValue (B.graphBundle.tensorPower (2 * t)) (y c) (a j) := by
      change Rational.LineBundleEvaluation.rationalLineBundleSectionValue (B.graphBundle.tensorPower (2 * t)) (y c)
        ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap B.abelian.scheme.hom)
          (B.graphBundle.tensorPower (2 * t)).sheaf).symm (b j)) = _
      exact congrArg (Rational.LineBundleEvaluation.rationalLineBundleSectionValue (B.graphBundle.tensorPower (2 * t)) (y c))
        (congrFun hb j)
    rw [hc]
    calc
      _ = Geometric.FrameOpenCover.fieldPointGlobalScalarMap (𝟙 (Spec (.of K)))
          (q.appTop (Family.FramedSectionEvaluation.familyFramedSectionValue L (x c) (e c) (s j))) := by
        simp only [Geometric.FrameOpenCover.fieldPointGlobalScalarMap, Scheme.Hom.id_appTop, RingHom.comp_apply]
        rfl
      _ = Geometric.FrameOpenCover.fieldPointGlobalScalarMap (𝟙 (Spec (.of K)))
          (Family.FramedSectionEvaluation.familyFramedSectionValue (L.pullback π) (y c) (e₀ c) (Ample.LineBundles.pullbackSection π (s j))) :=
        congrArg (Geometric.FrameOpenCover.fieldPointGlobalScalarMap (𝟙 (Spec (.of K))))
          (Family.FramedEvaluationBaseChange.familyFramedSectionValue_baseChange L q π (x c) (y c) (hy c) (e c) (s j)).symm
      _ = Geometric.FrameOpenCover.fieldPointGlobalScalarMap (𝟙 (Spec (.of K)))
          (Family.FramedSectionEvaluation.familyFramedSectionValue (B.graphBundle.tensorPower (2 * t)) (y c) (e₁ c) (a j)) :=
        congrArg (Geometric.FrameOpenCover.fieldPointGlobalScalarMap (𝟙 (Spec (.of K))))
          (Framed.SectionBundleTransport.familyFramedSectionValue_bundleIso (y c) H (e₀ c) (Ample.LineBundles.pullbackSection π (s j))).symm
      _ = _ := hz c (a j)
  rw [heq]
  exact BasisEvaluationMatrices.matrix_rowUnits_injective F z hF

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphFamilyEvaluationMatrix.PolarizedAbelianWithLevel
