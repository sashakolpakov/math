import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.PrimeExtension

/-! # Line Vertical Divisors -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.LineVerticalDivisors.BundleCycles

noncomputable section

/-! # LineBundleCycles: every vertical codimension-one affine-line point is the actual generic point of its fiber -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem affineLineVerticalHeightOne_generic (y : Charts.BundleCycles.affineLine X) (hy : Order.coheight y = 1)
    (hbase : Charts.BundleCycles.affineLineProjection X y ≠ genericPoint X) :
    Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) (Charts.BundleCycles.affineLineProjection X y) = y := by
  obtain ⟨U, P, rfl⟩ := Charts.BundleCycles.affineLinePolynomialChart_covers X y
  have hu : U.2.fromSpec (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P) ∈ (U.1 : Set X) :=
    U.2.range_fromSpec ▸ Set.mem_range_self (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P)
  have : Nonempty U.1 := ⟨⟨_, hu⟩⟩
  have hPheight : P.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight]
    exact (coheight_eq_of_isOpenImmersion (Charts.BundleCycles.affineLinePolynomialChart X U)).symm.trans hy
  have hPbase : P.asIdeal.comap Polynomial.C ≠ ⊥ := by
    intro h
    apply hbase
    apply (HorizontalCharts.BundleCycles.affineLinePolynomialChart_base_generic_iff X U P).mpr
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext h
  let : P.asIdeal.IsPrime := (show PrimeSpectrum (Polynomial Γ(X, U.1)) from P).isPrime
  have hP : LineBundles.Polynomial.Projection.BundleCycles.polynomialPrimePoint Γ(X, U.1) (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P) = P :=
    PrimeSpectrum.ext (LineBundles.Polynomial.PrimeExtension.BundleCycles.polynomialHeightOne_isExtended P.asIdeal hPheight hPbase)
  have hb := congrArg (fun k => k P) (Charts.BundleCycles.affineLinePolynomialChart_toBase X U)
  exact (congrArg (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) hb).trans
    ((GenericPoint.BundleCycles.affineLineFiberGenericPoint_on_chart X U (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P)).trans
      (congrArg (Charts.BundleCycles.affineLinePolynomialChart X U) hP))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.LineVerticalDivisors.BundleCycles
