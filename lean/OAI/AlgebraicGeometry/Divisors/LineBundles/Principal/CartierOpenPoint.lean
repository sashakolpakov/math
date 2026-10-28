import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RestrictionOpenDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportRegularFunction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueSupport

/-! # Cartier Open Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierOpenPoint.BundleCycles

noncomputable section

/-! The complete principal intersection divisor restricts along an actual open immersion, including every point coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y] (i : X ⟶ Y) [IsOpenImmersion i]

theorem principalCartierPointCycle_open (a : Γ(Y, ⊤)) (x : X) :
    Finsupp.comapDomain i (CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm (i x)))
      i.isOpenEmbedding.injective.injOn =
      CartierCycle.BundleCycles.principalCartierPointCycle (i.appTop a) (irreducibleSetEquivPoints.symm x) :=
  (Normal.RestrictionOpenDivisor.BundleCycles.pointSupportPrincipalDivisor_open i x _).trans
    (congrArg (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x))
      (Point.SupportRegularFunction.BundleCycles.pointSupportFunctionFieldMap_regular i x a))

theorem principalCartierPointMap_open (a : Γ(Y, ⊤)) (z : Y →₀ ℚ) :
    Finsupp.comapDomain i (CartierFiber.BundleCycles.principalCartierPointMap a z) i.isOpenEmbedding.injective.injOn =
      CartierFiber.BundleCycles.principalCartierPointMap (i.appTop a)
        (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) := by
  let L : (Y →₀ ℚ) →ₗ[ℚ] (X →₀ ℚ) := Finsupp.lcomapDomain i i.isOpenEmbedding.injective
  change L (CartierFiber.BundleCycles.principalCartierPointMap a z) = CartierFiber.BundleCycles.principalCartierPointMap (i.appTop a) (L z)
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | single y q =>
    by_cases hy : y ∈ Set.range i
    · obtain ⟨x, rfl⟩ := hy
      have hs : L (Finsupp.single (i x) q) = Finsupp.single x q :=
        Finsupp.comapDomain_single i x q i.isOpenEmbedding.injective.injOn
      rw [CartierFiber.BundleCycles.principalCartierPointMap_single, map_smul, hs, CartierFiber.BundleCycles.principalCartierPointMap_single]
      exact congrArg (fun c => q • c) (principalCartierPointCycle_open i a x)
    · have hs : L (Finsupp.single y q) = 0 := by
        apply Finsupp.comapDomain_single_of_not_mem_range
        exact hy
      have hc : L (CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm y)) = 0 := by
        ext x
        exact Open.PrincipalRestriction.BundleCycles.schemePrincipalPointDivisor_off_support _ _ (i x) (LineBundle.ProperResidueSupport.Cycles.pointSupport_off_open i y hy x)
      rw [hs, map_zero, CartierFiber.BundleCycles.principalCartierPointMap_single, map_smul, hc, smul_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierOpenPoint.BundleCycles
