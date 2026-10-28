import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.FunctionField
import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DeformationFlat
import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.DivisorPullback

/-! # Divisor Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DivisorPullback.BundleCycles

noncomputable section

/-! # LineBundleCycles: complete global rational-divisor pullback to the punctured deformation -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def puncturedCycleExtension : (X →₀ ℚ) →ₗ[ℚ] (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I)

variable [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem puncturedOrder_on_chart (U : X.AffineZariskiSite) [Nonempty U.1]
    (g : X.functionField) (P : Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1)))) :
    (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I).ord (FunctionField.BundleCycles.puncturedFunctionFieldMap I g) (DeformationCharts.BundleCycles.puncturedLaurentChart I U P) =
      (Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1)))).ord
        (Laurent.FiberGenericPoint.BundleCycles.laurentFunctionFieldMap Γ(X, U.1) (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec g)) P := by
  have h := congrArg (fun k => k g) (FunctionField.BundleCycles.puncturedFunctionFieldMap_on_chart I U)
  exact (RationalDivisorRestriction.BundleCycles.ord_openImmersion (DeformationCharts.BundleCycles.puncturedLaurentChart I U) (FunctionField.BundleCycles.puncturedFunctionFieldMap I g) P).symm.trans
    (congrArg (fun a => (Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1)))).ord a P) h)

theorem puncturedProjection_order (x : X) (g : X.functionField) :
    (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I).ord (FunctionField.BundleCycles.puncturedFunctionFieldMap I g) (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I x) =
      X.ord g x := by
  let U : X.AffineZariskiSite := (directedCover X).idx x
  obtain ⟨y, hy⟩ := (directedCover X).covers x
  have hx : x ∈ (U.1 : Set X) := hy ▸ y.property
  have : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  obtain ⟨p, hp⟩ := (congrArg (fun s : Set X => x ∈ s) U.2.range_fromSpec).mpr hx
  have he := DeformationFlat.BundleCycles.puncturedFiberGenericPoint_on_chart I U p
  rw [hp] at he
  rw [he]
  exact (puncturedOrder_on_chart I U g (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint Γ(X, U.1) p)).trans
    ((Laurent.DivisorPullback.BundleCycles.laurentProjection_order Γ(X, U.1) p (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec g)).trans
      ((RationalDivisorRestriction.BundleCycles.ord_openImmersion U.2.fromSpec g p).trans (congrArg (X.ord g) hp)))

theorem puncturedPulledDivisor_support (g : X.functionField) (hg : g ≠ 0)
    (y : Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I)
    (hy : (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I).ord (FunctionField.BundleCycles.puncturedFunctionFieldMap I g) y ≠ 0) :
    y ∈ Set.range (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I) := by
  obtain ⟨U, P, rfl⟩ := DeformationCharts.BundleCycles.puncturedLaurentChart_covers I y
  have hp : U.2.fromSpec (Laurent.FiberGenericPoint.BundleCycles.laurentProjection Γ(X, U.1) P) ∈ (U.1 : Set X) := by
    rw [← U.2.range_fromSpec]
    exact ⟨_, rfl⟩
  have : Nonempty U.1 := ⟨⟨_, hp⟩⟩
  have hg' : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec g ≠ 0 :=
    (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec).hom.injective).mpr hg
  have hP : (Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1)))).ord
      (Laurent.FiberGenericPoint.BundleCycles.laurentFunctionFieldMap Γ(X, U.1) (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec g)) P ≠ 0 :=
    fun hz => hy ((puncturedOrder_on_chart I U g P).trans hz)
  obtain ⟨p, rfl⟩ := Laurent.DivisorPullback.BundleCycles.laurentPulledDivisor_support Γ(X, U.1) _ hg' P hP
  exact ⟨U.2.fromSpec p, DeformationFlat.BundleCycles.puncturedFiberGenericPoint_on_chart I U p⟩

theorem puncturedPrincipalDivisor_pullback (g : X.functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I) (FunctionField.BundleCycles.puncturedFunctionFieldMap I g) =
      puncturedCycleExtension I (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) := by
  ext y
  by_cases hy : y ∈ Set.range (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I)
  · obtain ⟨x, rfl⟩ := hy
    change _ = Finsupp.mapDomain (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I) _ (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I x)
    rw [Finsupp.mapDomain_apply_of_injective (DeformationFlat.BundleCycles.puncturedFiberGenericPoint_injective I),
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, puncturedProjection_order]
  · have hz : (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I).ord (FunctionField.BundleCycles.puncturedFunctionFieldMap I g) y = 0 := by
      by_contra hn
      exact hy (puncturedPulledDivisor_support I g hg y hn)
    change _ = Finsupp.mapDomain (DeformationFlat.BundleCycles.puncturedFiberGenericPoint I) _ y
    rw [Finsupp.mapDomain_of_notMem_range _ _ hy, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, hz, Int.cast_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DivisorPullback.BundleCycles
