import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.GenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DivisorPullback

/-! # Divisor Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.DivisorPullback.BundleCycles

noncomputable section

/-! # LineBundleCycles: complete rational-divisor pullback to the relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme.{0})

variable [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem affineLineOrder_on_chart (U : X.affineOpens) [Nonempty U.1]
    (g : X.functionField) (P : Spec (CommRingCat.of (Polynomial Γ(X, U.1)))) :
    (Charts.BundleCycles.affineLine X).ord (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) g) (Charts.BundleCycles.affineLinePolynomialChart X U P) =
      (Spec (CommRingCat.of (Polynomial Γ(X, U.1)))).ord
        (LineBundles.Polynomial.Projection.BundleCycles.polynomialFunctionFieldMap Γ(X, U.1) (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec g)) P := by
  have h := congrArg (fun k => k g) (GenericPoint.BundleCycles.affineLineFunctionField_on_chart X U)
  exact (RationalDivisorRestriction.BundleCycles.ord_openImmersion (Charts.BundleCycles.affineLinePolynomialChart X U) (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) g) P).symm.trans
    (congrArg (fun a => (Spec (CommRingCat.of (Polynomial Γ(X, U.1)))).ord a P) h)

theorem affineLineProjection_order (x : X) (g : X.functionField) :
    (Charts.BundleCycles.affineLine X).ord (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) g) (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) =
      X.ord g x := by
  obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let U : X.affineOpens := ⟨V, hV⟩
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  obtain ⟨p, hp⟩ := (congrArg (fun s : Set X => x ∈ s) U.2.range_fromSpec).mpr hx
  have he := GenericPoint.BundleCycles.affineLineFiberGenericPoint_on_chart X U p
  rw [hp] at he
  rw [he]
  exact (affineLineOrder_on_chart X U g (LineBundles.Polynomial.Projection.BundleCycles.polynomialPrimePoint Γ(X, U.1) p)).trans
    ((LineBundles.Polynomial.DivisorPullback.BundleCycles.polynomialProjection_order Γ(X, U.1) p (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec g)).trans
      ((RationalDivisorRestriction.BundleCycles.ord_openImmersion U.2.fromSpec g p).trans (congrArg (X.ord g) hp)))

theorem affineLinePulledDivisor_support (g : X.functionField) (hg : g ≠ 0)
    (y : Charts.BundleCycles.affineLine X)
    (hy : (Charts.BundleCycles.affineLine X).ord (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) g) y ≠ 0) :
    y ∈ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) := by
  obtain ⟨U, P, rfl⟩ := Charts.BundleCycles.affineLinePolynomialChart_covers X y
  have hp : U.2.fromSpec (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P) ∈ (U.1 : Set X) := by
    rw [← U.2.range_fromSpec]
    exact ⟨_, rfl⟩
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have : Nonempty U.1 := ⟨⟨_, hp⟩⟩
  have hg' : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec g ≠ 0 :=
    (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec).hom.injective).mpr hg
  have hP : (Spec (CommRingCat.of (Polynomial Γ(X, U.1)))).ord
      (LineBundles.Polynomial.Projection.BundleCycles.polynomialFunctionFieldMap Γ(X, U.1) (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec g)) P ≠ 0 :=
    fun hz => hy ((affineLineOrder_on_chart X U g P).trans hz)
  obtain ⟨p, rfl⟩ := LineBundles.Polynomial.DivisorPullback.BundleCycles.polynomialPulledDivisor_support Γ(X, U.1) _ hg' P hP
  exact ⟨U.2.fromSpec p, GenericPoint.BundleCycles.affineLineFiberGenericPoint_on_chart X U p⟩

theorem affineLinePrincipalDivisor_pullback (g : X.functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) g) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) := by
  ext y
  by_cases hy : y ∈ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X))
  · obtain ⟨x, rfl⟩ := hy
    change _ = Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) _ (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x)
    rw [Finsupp.mapDomain_apply_of_injective (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective (Charts.BundleCycles.affineLineProjection X)),
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, affineLineProjection_order]
  · have hz : (Charts.BundleCycles.affineLine X).ord (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) g) y = 0 := by
      by_contra hn
      exact hy (affineLinePulledDivisor_support X g hg y hn)
    change _ = Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) _ y
    rw [Finsupp.mapDomain_of_notMem_range _ _ hy, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, hz, Int.cast_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.DivisorPullback.BundleCycles
