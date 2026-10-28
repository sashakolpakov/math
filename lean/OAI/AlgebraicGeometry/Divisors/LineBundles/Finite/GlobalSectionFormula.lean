import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSupportNeighborhood
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionCommonRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportOpenAnalyticDetection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.OpenRestrictionComposition

/-! # Global Section Formula -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionFormula.BundleCycles

noncomputable section

/-! The genuine global finite-image section cup is the canonical supported class of the full principal divisor pushforward, with all orders and residue degrees, across the singular and exceptional boundaries. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral N.left] [Smooth N.hom]
  [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)]
  (k : S ⟶ N) [IsFinite k.left] (s : Γ(N.left, ⊤)) (p : ℕ)
  (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)
  (n : ℕ) (hn : n + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom)

local instance finiteGlobalSectionFormulaTop : Nonempty (⊤ : S.left.Opens) :=
  ⟨⟨genericPoint S.left, Opens.mem_top _⟩⟩

variable (hs : S.left.germToFunctionField ⊤ (k.left.appTop s) ≠ 0)

include hs in
theorem finiteGlobalSectionCup_eq_principalSupportedClass :
    GlobalSectionClassRestriction.BundleCycles.finiteGlobalSectionCup k s p hp = RegularSupportedClassRestriction.BundleCycles.finiteRegularPrincipalSupportedClass k s p hp n hn := by
  classical
  let F := SectionCommonRestriction.BundleCycles.finiteRegularSectionClosed k s
  let A := (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ
  let V := PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen (S.left.germToFunctionField ⊤ (k.left.appTop s)) k
  let Z := {x : V // ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ F}
  have existsU (z : Z) : ∃ U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N), z.val.val ∈ U ∧ U ≤ V ∧
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) A U (2 * (p + 1))
        (GlobalSectionClassRestriction.BundleCycles.finiteGlobalSectionCup k s p hp) =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) A U (2 * (p + 1))
        (RegularSupportedClassRestriction.BundleCycles.finiteRegularPrincipalSupportedClass k s p hp n hn) := by
    apply GlobalSupportNeighborhood.BundleCycles.finiteGlobalSection_exists_support_neighborhood k s p hp n hn hs z.val.val
    · exact (Set.ext_iff.mp (SectionCommonRestriction.BundleCycles.finiteRegularSectionClosed_analytic k s) z.val.val).mp z.property
    · exact z.val.property
  let U (z : Z) := Classical.choose (existsU z)
  have hU (z : Z) := Classical.choose_spec (existsU z)
  let := SectionCommonRestriction.BundleCycles.finiteSectionCommonRestriction_isIso k s p hp
  apply (asIso (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
    A V (2 * (p + 1)))).toLinearEquiv.injective
  have hA : A = (CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen N F.compl : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) :=
    (congrArg Set.compl (SectionCommonRestriction.BundleCycles.finiteRegularSectionClosed_analytic k s)).symm
  apply Closed.SupportOpenAnalyticDetection.BundleCycles.closedSupportedSetClass_on_open_eq_of_neighborhoods N F (p + 1)
    (SectionCommonRestriction.BundleCycles.finiteRegularSectionClosed_codimension k s hs p hp) A hA V U
    (fun z => (hU z).2.1) (fun z => (hU z).1)
  intro z
  have hleft := Relative.OpenRestrictionComposition.BundleCycles.relativeOpenRestriction_nested (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) A (U z) V
    (hU z).2.1 (2 * (p + 1)) (GlobalSectionClassRestriction.BundleCycles.finiteGlobalSectionCup k s p hp)
  have hright := Relative.OpenRestrictionComposition.BundleCycles.relativeOpenRestriction_nested (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) A (U z) V
    (hU z).2.1 (2 * (p + 1)) (RegularSupportedClassRestriction.BundleCycles.finiteRegularPrincipalSupportedClass k s p hp n hn)
  exact hleft.trans ((hU z).2.2.trans hright.symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionFormula.BundleCycles
