import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource

/-! # Albanese Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseLift.CM

noncomputable section

/-!
# Matching theta classes with the ambient Albanese

IntegralModel uses a product of component Albanese varieties. For its chosen factor,
the inclusion i and projection p satisfy i ≫ p = id. HodgeComparison supplies bijectivity
of the actual Albanese pullback a*. This file constructs the rational Hodge
lift p* (a*)⁻¹ and proves that restriction along a ≫ i recovers the original
class. No lift, matching equation, or Hodge compatibility is assumed.
-/

open _root_.CategoryTheory
open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

abbrev bettiPullback {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : X.toOver ⟶ Y.toOver) :
    Y.rationalCohomology 1 →ₗ[ℚ] X.rationalCohomology 1 :=
  (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f).hom

theorem bettiPullback_comp {X Y Z : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (g : Y.toOver ⟶ Z.toOver) :
    bettiPullback (f ≫ g) = (bettiPullback f).comp (bettiPullback g) := by
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_comp f g 1) x

theorem bettiPullback_id (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    bettiPullback (𝟙 X.toOver) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_id X 1) x

/-- Inverting a bijective rational Hodge map preserves Hodge type. -/
theorem hodge_inverse
    {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (J : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    (e : U ≃ₗ[ℚ] V) (he : ComplexMultiplication.WeightOne.CM.IsHodgeMap H J e.toLinearMap) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap J H e.symm.toLinearMap := by
  intro y hy
  change (e.symm.baseChange ℚ ℂ V U) y ∈ H.holomorphic
  rw [LinearEquiv.baseChange_symm]
  let ec := e.baseChange ℚ ℂ U V
  obtain ⟨u, v, huv, _⟩ := Submodule.existsUnique_add_of_isCompl
    H.complementary (ec.symm y)
  have hu : ec u ∈ J.holomorphic := he u u.property
  have hv : ec v ∈ J.antiholomorphic := he.map_antiholomorphic v.property
  have hadd : ec u + ec v = y := by rw [← map_add, huv, ec.apply_symm_apply]
  have hvh : ec v ∈ J.holomorphic := by
    rw [eq_sub_of_add_eq' hadd]
    exact J.holomorphic.sub_mem hy hu
  have hvzero : ec v = 0 := Submodule.disjoint_def.mp J.complementary.disjoint _ hvh hv
  have hvzero' : (v : ComplexMultiplication.WeightOne.CM.Complexification U) = 0 := ec.injective (hvzero.trans ec.map_zero.symm)
  change ec.symm y ∈ H.holomorphic
  rw [← huv, hvzero', add_zero]
  exact u.property

variable {X A Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}

def albaneseLift (a : X.toOver ⟶ A.toOver)
    (h_HodgeComparison : Function.Bijective (bettiPullback a)) (p : Y.toOver ⟶ A.toOver) :
    X.rationalCohomology 1 →ₗ[ℚ] Y.rationalCohomology 1 :=
  (bettiPullback p).comp (LinearEquiv.ofBijective (bettiPullback a) h_HodgeComparison).symm.toLinearMap

theorem restrict_albaneseLift
    (a : X.toOver ⟶ A.toOver) (h_HodgeComparison : Function.Bijective (bettiPullback a))
    (i : A.toOver ⟶ Y.toOver) (p : Y.toOver ⟶ A.toOver)
    (h_product : i ≫ p = 𝟙 A.toOver) :
    (bettiPullback (a ≫ i)).comp (albaneseLift a h_HodgeComparison p) = LinearMap.id := by
  have hip : (bettiPullback i).comp (bettiPullback p) = LinearMap.id := by
    rw [← bettiPullback_comp, h_product, bettiPullback_id]
  let e := LinearEquiv.ofBijective (bettiPullback a) h_HodgeComparison
  apply LinearMap.ext
  intro x
  rw [bettiPullback_comp]
  change bettiPullback a (bettiPullback i (bettiPullback p (e.symm x))) = x
  exact (congrArg (bettiPullback a) (LinearMap.congr_fun hip (e.symm x))).trans
    (e.apply_symm_apply x)

/-- The supplied Hodge structures are anchored to the actual geometric
holomorphic Betti pieces, exactly as in HodgeComparison.IsCanonicalH1. -/
def CanonicalHolomorphic (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1)) : Prop :=
  H.holomorphic = (X.pureBettiSubspace 1 0).comap
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1)

theorem albaneseLift_isHodgeMap
    (a : X.toOver ⟶ A.toOver) (h_HodgeComparison : Function.Bijective (bettiPullback a))
    (p : Y.toOver ⟶ A.toOver)
    (HX : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
    (HA : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.rationalCohomology 1))
    (HY : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Y.rationalCohomology 1))
    (hX : CanonicalHolomorphic X HX) (hA : CanonicalHolomorphic A HA)
    (hY : CanonicalHolomorphic Y HY) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap HX HY (albaneseLift a h_HodgeComparison p) := by
  apply ComplexMultiplication.WeightOne.CM.IsHodgeMap.comp (GeometricSource.CM.actual_restriction_isHodgeMap p HY HA hY hA)
  exact hodge_inverse HA HX (LinearEquiv.ofBijective (bettiPullback a) h_HodgeComparison)
    (GeometricSource.CM.actual_restriction_isHodgeMap a HX HA hX hA)

/-- Construct the holomorphic ambient theta class and the exact restriction
equation from HodgeComparison and the actual product-factor maps in IntegralModel. -/
theorem lift_theta_and_restrict
    (a : X.toOver ⟶ A.toOver) (h_HodgeComparison : Function.Bijective (bettiPullback a))
    (i : A.toOver ⟶ Y.toOver) (p : Y.toOver ⟶ A.toOver)
    (h_product : i ≫ p = 𝟙 A.toOver)
    (HX : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
    (HA : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.rationalCohomology 1))
    (HY : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Y.rationalCohomology 1))
    (hX : CanonicalHolomorphic X HX) (hA : CanonicalHolomorphic A HA)
    (hY : CanonicalHolomorphic Y HY)
    (Θ : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1)) (hΘ : Θ ∈ HX.holomorphic) :
    let theta := (albaneseLift a h_HodgeComparison p).baseChange ℂ Θ
    theta ∈ HY.holomorphic ∧ (bettiPullback (a ≫ i)).baseChange ℂ theta = Θ := by
  refine ⟨albaneseLift_isHodgeMap a h_HodgeComparison p HX HA HY hX hA hY Θ hΘ, ?_⟩
  have h := congrArg
    (fun f : Module.End ℚ (X.rationalCohomology 1) => f.baseChange ℂ)
    (restrict_albaneseLift a h_HodgeComparison i p h_product)
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at h
  exact LinearMap.congr_fun h Θ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseLift.CM
