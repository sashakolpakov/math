import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SectionNeighborhood
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionClassRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RegularSupportedClassRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentSection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenClassSupportTransport

/-! # Global Section Neighborhood -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionNeighborhood.BundleCycles

noncomputable section

/-! Every retained point of an actual affine chart has a neighborhood where the two original global supported classes agree. All graph, divisor, coefficient, and support comparisons are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral N.left] [Smooth N.hom]
  [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)]
  (k : S ⟶ N) [IsFinite k.left] (B : N.left.Opens)
  [Nonempty B] [Nonempty (k.left ⁻¹ᵁ B)] [IsAffine (FiniteAffine.OpenChart.BundleCycles.finiteAffineBase B).left]
  (s : Γ(N.left, ⊤)) (p : ℕ)
  (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)
  (n : ℕ) (hn : n + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom)

local instance finiteGlobalSectionNeighborhoodSourceTop : Nonempty (⊤ : S.left.Opens) :=
  ⟨⟨genericPoint S.left, Opens.mem_top _⟩⟩
local instance finiteGlobalSectionNeighborhoodChartTop : Nonempty (⊤ : (FiniteAffine.OpenChart.BundleCycles.finiteAffineSource k B).left.Opens) :=
  ⟨⟨genericPoint (FiniteAffine.OpenChart.BundleCycles.finiteAffineSource k B).left, Opens.mem_top _⟩⟩

variable (hs : S.left.germToFunctionField ⊤ (k.left.appTop s) ≠ 0)

include hs in
theorem finiteGlobalSection_exists_affine_neighborhood (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (FiniteAffine.OpenChart.BundleCycles.finiteAffineBase B))
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteAffine.OpenChart.BundleCycles.finiteAffineBaseInclusion B) x ∈
      PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen (S.left.germToFunctionField ⊤ (k.left.appTop s)) k) :
    ∃ U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N),
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteAffine.OpenChart.BundleCycles.finiteAffineBaseInclusion B) x ∈ U ∧
      (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen (S.left.germToFunctionField ⊤ (k.left.appTop s)) k ∧
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
        (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ U (2 * (p + 1)) (GlobalSectionClassRestriction.BundleCycles.finiteGlobalSectionCup k s p hp) =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
        (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ U (2 * (p + 1)) (RegularSupportedClassRestriction.BundleCycles.finiteRegularPrincipalSupportedClass k s p hp n hn) := by
  let a := FiniteAffine.OpenChart.BundleCycles.finiteAffineSourceInclusion k B
  let g := FiniteAffine.OpenChart.BundleCycles.finiteAffineMap k B
  let j := FiniteAffine.OpenChart.BundleCycles.finiteAffineBaseInclusion B
  have hfield := ParentSection.BundleCycles.finiteParentRationalFunction_baseSection a k g j (FiniteAffine.OpenChart.BundleCycles.finiteAffineChart_square k B) s
  have hnonzero := ParentSection.BundleCycles.finiteChart_globalSection_germ_ne_zero k a g j (FiniteAffine.OpenChart.BundleCycles.finiteAffineChart_square k B) s hs
  have hx' : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j x ∈ PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen
      (ParentSection.BundleCycles.finiteParentRationalFunction a ((FiniteAffine.OpenChart.BundleCycles.finiteAffineSource k B).left.germToFunctionField ⊤ (g.left.appTop (j.left.appTop s)))) k := by
    rw [hfield]
    exact hx
  obtain ⟨U, hU, hxU, hgood, he⟩ := FiniteAffine.SectionNeighborhood.BundleCycles.finiteAffine_exists_section_principal_neighborhood k B p hp
    (j.left.appTop s) hnonzero n hn x hx'
  rw [hfield] at hgood
  refine ⟨U, hxU, hgood, ?_⟩
  have hraw := ParentSection.BundleCycles.finiteParentPrincipalCycle_baseSection k a g j (FiniteAffine.OpenChart.BundleCycles.finiteAffineChart_square k B) n s
  rw [hraw] at he
  have hT := GlobalSectionSupportRestriction.BundleCycles.globalSection_finiteIntersection_range j U hU s k
  let e := CycleClass.Thom.Supported.Transport.Constructions.Class.supportDegreeTransport (n := 2 * (p + 1)) (TopCat.of U) (congrArg Set.compl hT.symm) rfl
  apply CycleClass.Thom.Supported.Transport.Constructions.Class.supportDegreeTransport_injective (n := 2 * (p + 1)) (TopCat.of U) (congrArg Set.compl hT.symm) rfl
  have hleft := CycleClass.Thom.ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
    (congrArg Set.compl hT.symm)
    (show Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
      (Subtype.val ⁻¹' RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ from fun _ hy => hy)
    (GlobalSectionClassRestriction.BundleCycles.finiteGlobalSectionCup_mapsTo k s j U hU) (2 * (p + 1)) (GlobalSectionClassRestriction.BundleCycles.finiteGlobalSectionCup k s p hp)
  have hright := RegularSupportedClassRestriction.BundleCycles.finiteRegularPrincipalSupportedClass_restrict k s p hp n hn U
  have ht := Scheme.OpenClassSupportTransport.BundleCycles.schemeOpenRestrictedClass_supportTransport N U
    (Subtype.val ⁻¹' RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s) _ hT.symm n (p + 1) hn
    (GradedOverPushforward.BundleCycles.finiteOverGradedPushforward k n (Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor S.left S.hom n
      (S.left.germToFunctionField ⊤ (k.left.appTop s))))
  exact hleft.trans ((GlobalSectionClassRestriction.BundleCycles.finiteGlobalSectionCup_restriction k s p hp j U hU).trans
    (he.trans (ht.symm.trans (congrArg e hright.symm))))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionNeighborhood.BundleCycles
