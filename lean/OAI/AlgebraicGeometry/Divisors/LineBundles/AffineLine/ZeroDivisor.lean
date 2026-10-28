import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroMultiplicity
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroLocus
import OAI.AlgebraicGeometry.Divisors.LineBundles.DivisorRestriction

/-! # Zero Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: the global coordinate divisor is the reduced zero section with coefficient one -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [IsIntegral X]

theorem affineLineCoordinate_ne_zero : Space.BundleCycles.affineLineCoordinate X ≠ 0 := by
  let x : X := genericPoint X
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let V : X.affineOpens := ⟨U, hU⟩
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  intro h
  apply Polynomial.ZeroMultiplicity.BundleCycles.polynomialCoordinateSection_ne_zero Γ(X, U)
  exact (Space.BundleCycles.affineLineCoordinate_on_chart X V).symm.trans
    ((congrArg (Charts.BundleCycles.affineLinePolynomialChart X V).appTop h).trans (map_zero _))

theorem affineLineZeroPrime_on_chart (U : X.affineOpens) [Nonempty U.1] :
    Charts.BundleCycles.affineLinePolynomialChart X U (Polynomial.ZeroPrime.BundleCycles.polynomialZeroPrime Γ(X, U.1)) = Space.BundleCycles.affineLineZeroSection X (genericPoint X) := by
  have h := congrArg (fun k => k (genericPoint (Spec Γ(X, U.1))))
    (ZeroLocus.BundleCycles.affineLineZeroSection_chart_isPullback X U).w
  exact h.symm.trans (congrArg (Space.BundleCycles.affineLineZeroSection X) (genericPoint_eq_of_isOpenImmersion U.2.fromSpec))

variable [AlgebraicGeometry.IsNoetherian X]

theorem affineLineZeroDivisor_eq_single :
    RegularDivisor.BundleCycles.regularFunctionDivisor (Charts.BundleCycles.affineLine X) (Space.BundleCycles.affineLineCoordinate X) =
      Finsupp.single (Space.BundleCycles.affineLineZeroSection X (genericPoint X)) 1 := by
  ext y
  obtain ⟨U, P, rfl⟩ := Charts.BundleCycles.affineLinePolynomialChart_covers X y
  have hu : U.2.fromSpec (Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P) ∈ (U.1 : Set X) :=
    U.2.range_fromSpec ▸ Set.mem_range_self (Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P)
  have : Nonempty U.1 := ⟨⟨_, hu⟩⟩
  have h := DivisorRestriction.BundleCycles.regularFunctionDivisor_openImmersion (Charts.BundleCycles.affineLinePolynomialChart X U)
    (Space.BundleCycles.affineLineCoordinate X) (affineLineCoordinate_ne_zero X) P
  rw [Space.BundleCycles.affineLineCoordinate_on_chart, Polynomial.ZeroMultiplicity.BundleCycles.polynomialZeroDivisor_eq_single] at h
  rw [← h, ← affineLineZeroPrime_on_chart X U]
  have hm := Finsupp.mapDomain_apply_of_injective (Charts.BundleCycles.affineLinePolynomialChart X U).isOpenEmbedding.injective
    (Finsupp.single (Polynomial.ZeroPrime.BundleCycles.polynomialZeroPrime Γ(X, U.1)) (1 : ℤ)) P
  simpa only [Finsupp.mapDomain_single] using hm.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroDivisor.BundleCycles
