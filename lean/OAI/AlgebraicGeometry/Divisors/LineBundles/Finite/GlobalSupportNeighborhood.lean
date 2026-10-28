import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionNeighborhood
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionAffineChart

/-! # Global Support Neighborhood -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSupportNeighborhood.BundleCycles

noncomputable section

/-! Every point of the retained actual section intersection has a neighborhood where the original global supported cup and full principal-cycle class agree. The affine chart is constructed from the point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral N.left] [Smooth N.hom]
  [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)]
  (k : S ⟶ N) [IsFinite k.left] (s : Γ(N.left, ⊤)) (p : ℕ)
  (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)
  (n : ℕ) (hn : n + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom)

local instance finiteGlobalSupportNeighborhoodTop : Nonempty (⊤ : S.left.Opens) :=
  ⟨⟨genericPoint S.left, Opens.mem_top _⟩⟩

variable (hs : S.left.germToFunctionField ⊤ (k.left.appTop s) ≠ 0)

include hs in
theorem finiteGlobalSection_exists_support_neighborhood (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)
    (hyF : y ∈ RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)
    (hy : y ∈ PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen (S.left.germToFunctionField ⊤ (k.left.appTop s)) k) :
    ∃ U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N), y ∈ U ∧
      (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen (S.left.germToFunctionField ⊤ (k.left.appTop s)) k ∧
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
        (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ U (2 * (p + 1)) (GlobalSectionClassRestriction.BundleCycles.finiteGlobalSectionCup k s p hp) =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
        (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ U (2 * (p + 1)) (RegularSupportedClassRestriction.BundleCycles.finiteRegularPrincipalSupportedClass k s p hp n hn) := by
  obtain ⟨B, hB, hneB, hneS, x, hx⟩ := SectionAffineChart.BundleCycles.finiteParentPoint_exists_affine_chart k y hyF.1
  let : IsAffine (FiniteAffine.OpenChart.BundleCycles.finiteAffineBase B).left := hB
  let : Nonempty B := hneB
  let : Nonempty (k.left ⁻¹ᵁ B) := hneS
  have hx' : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteAffine.OpenChart.BundleCycles.finiteAffineBaseInclusion B) x ∈
      PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen (S.left.germToFunctionField ⊤ (k.left.appTop s)) k := hx.symm ▸ hy
  obtain ⟨U, hyU, hgood, he⟩ := GlobalSectionNeighborhood.BundleCycles.finiteGlobalSection_exists_affine_neighborhood k B s p hp n hn hs x hx'
  exact ⟨U, hx ▸ hyU, hgood, he⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSupportNeighborhood.BundleCycles
