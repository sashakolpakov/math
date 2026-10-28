import OAI.AlgebraicGeometry.HodgeConjecture.Surface
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Chow

/-! # Poincare -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Poincare.CM.SurfaceConstruction

noncomputable section

/-! Supply ProjectionFormula's Poincare interface from the canonical fundamental class
and proved native duality; identify its even-degree push with Functoriality. -/

open _root_.CategoryTheory

theorem nativePoincare_apply (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (h : p + q = 2 * X.complexDimension) (a : X.rationalCohomology p) :
    (X.poincareDuality p q h).hom a =
      AlgebraicTopology.Products.CapBoundary.singularCapHomology (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) p q a
        (SurfaceConstructionQ.CM.fundamentalQInDegree X (p + q) h.symm) := by
  change AlgebraicTopology.Products.CapBoundary.singularCapHomology (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) p q a
    (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) _ _ _) = _
  apply congrArg (AlgebraicTopology.Products.CapBoundary.singularCapHomology (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) p q a)
  exact Surface.CM.Construction.integralToRational_degreeCast (TopCat.of X.analyticSpace) h.symm
    (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass X.complexDimension X.analyticSpace)

def nativePoincareData (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    IntersectionTheory.ProjectionFormula.Definitions.PoincareData (Betti.Scheme.schemePointSpace X.toOver) (2 * X.complexDimension) where
  fundamental := SurfaceConstructionQ.CM.fundamentalQ X
  duality p q h := (X.poincareDuality p q h).toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℚ _ ((-1 : ℚ) ^ (p * q)) (by positivity))
  duality_apply p q h a := by
    change (-1 : ℚ) ^ (p * q) • (X.poincareDuality p q h).hom a = _
    rw [nativePoincare_apply]
    rfl

theorem nativePoincareData_even (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (h : (p + p) + q = 2 * X.complexDimension) (a : X.rationalCohomology (p + p)) :
    (nativePoincareData X).duality (p + p) q h a = (X.poincareDuality (p + p) q h).hom a := by
  change (-1 : ℚ) ^ ((p + p) * q) • (X.poincareDuality (p + p) q h).hom a = _
  rw [add_mul, pow_add]
  have hsq : (-1 : ℚ) ^ (p * q) * (-1 : ℚ) ^ (p * q) = 1 := by
    rw [← mul_pow]
    simp
  rw [hsq, one_smul]

theorem nativePushforward_eq_Functoriality {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (p q r : ℕ)
    (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (hX : (p + p) + r = 2 * X.complexDimension)
    (hY : (q + q) + r = 2 * Y.complexDimension)
    (a : X.rationalCohomology (p + p)) :
    IntersectionTheory.ProjectionFormula.Definitions.pushforward (nativePoincareData X) (nativePoincareData Y)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) (p + p) (q + q) r hX hY a =
      Cycles.Functoriality.UnitCap.cohomologyPushforward f (SurfaceConstructionQ.CM.map_isProper f) p q hdeg a := by
  have hp : p ≤ X.complexDimension := by omega
  have hr : r = 2 * (X.complexDimension - p) := by omega
  subst r
  apply (nativePoincareData Y).duality (q + q) _ hY |>.injective
  unfold IntersectionTheory.ProjectionFormula.Definitions.pushforward
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]
  rw [nativePoincareData_even, nativePoincareData_even]
  erw [Cycles.Functoriality.UnitCap.cohomologyPushforward_eq_poincare f (SurfaceConstructionQ.CM.map_isProper f) p q hdeg hp]
  change _ = (Y.poincareDuality (q + q) _ _).hom
    ((Y.poincareDuality (q + q) _ _).inv _)
  exact (Iso.inv_hom_id_apply (Y.poincareDuality (q + q) _ _) _).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.Poincare.CM.SurfaceConstruction
