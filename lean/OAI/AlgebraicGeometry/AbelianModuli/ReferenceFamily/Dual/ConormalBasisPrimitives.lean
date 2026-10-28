import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ConormalCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductPrimitiveCriterion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGauge

/-! # Conormal Basis Primitives -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalBasisPrimitives

noncomputable section

section

/-! An actual normalized global product exists exactly when the
constructed conormal-valued regular transition cocycle has a primitive. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] CommonOpenCocycle.dualFamilyPairAffineOpen ChartGauge.dualFamilyChartAffineOpen
attribute [local implicit_reducible] ChartGauge.dualChartGaugeParameters

variable (X : Over (Spec (.of (DualNumber ℂ)))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left]
    [Smooth (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] [GrpObj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)]
    (U : X.left.AffineOpenCover)

abbrev dualConormalGaugeParameters := ∀ i : U.I₀,
  Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X) →ₗ[ℂ]
    HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (CommonOpenFiber.dualAffineCommonOpenFiber ℂ X (ChartGauge.dualFamilyChartAffineOpen ℂ X U i))

def dualConormalGaugeEquiv : ChartGauge.dualChartGaugeParameters ℂ X U ≃ₗ[ℂ] dualConormalGaugeParameters X U :=
  LinearEquiv.piCongrRight (fun i => DualAffine.ConormalCoordinates.dualAffineConormalLinearEquiv X (ChartGauge.dualFamilyChartAffineOpen ℂ X U i))

def IsDualConormalPrimitive (b : dualConormalGaugeParameters X U) : Prop := ∀ i j : U.I₀,
  ∀ z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X),
    DualAffine.ConormalCocycle.dualFamilyPairConormalTransition X U i j z =
      CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap ℂ X
        (show (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j).1 ≤ (ChartGauge.dualFamilyChartAffineOpen ℂ X U i).1 from inf_le_left)
          (b i z) -
      CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap ℂ X
        (show (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j).1 ≤ (ChartGauge.dualFamilyChartAffineOpen ℂ X U j).1 from inf_le_right)
          (b j z)

theorem dualConormalGaugeEquiv_primitive (a : ChartGauge.dualChartGaugeParameters ℂ X U) :
    ChartGaugePrimitive.IsDualChartGaugePrimitive ℂ X U a ↔ IsDualConormalPrimitive X U (dualConormalGaugeEquiv X U a) := by
  have h (i j : U.I₀) :
      CommonOpenCocycle.dualFamilyPairTransitionDerivation ℂ X U i j =
        ChartGauge.dualChartGaugeCoefficient ℂ X U a (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j) i inf_le_left -
          ChartGauge.dualChartGaugeCoefficient ℂ X U a (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j) j inf_le_right ↔
      ∀ z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X),
        DualAffine.ConormalCocycle.dualFamilyPairConormalTransition X U i j z =
          CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap ℂ X
            (show (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j).1 ≤ (ChartGauge.dualFamilyChartAffineOpen ℂ X U i).1 from inf_le_left)
              (DualAffine.ConormalCoordinates.dualAffineConormalLinearEquiv X (ChartGauge.dualFamilyChartAffineOpen ℂ X U i) (a i) z) -
          CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap ℂ X
            (show (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j).1 ≤ (ChartGauge.dualFamilyChartAffineOpen ℂ X U j).1 from inf_le_right)
              (DualAffine.ConormalCoordinates.dualAffineConormalLinearEquiv X (ChartGauge.dualFamilyChartAffineOpen ℂ X U j) (a j) z) := by
    rw [← (DualAffine.ConormalCoordinates.dualAffineConormalLinearEquiv X (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j)).injective.eq_iff,
      map_sub, LinearMap.ext_iff]
    apply forall_congr'
    intro z
    simp only [LinearMap.sub_apply, ChartGauge.dualChartGaugeCoefficient, DualAffine.ConormalCoordinates.dualAffineConormalLinearEquiv_natural]
    rfl
  exact forall_congr' (fun i => forall_congr' (fun j => h i j))

theorem normalizedDualProduct_iff_conormalPrimitive :
    (∃ e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X),
      NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e) ↔
    ∃ b : dualConormalGaugeParameters X U, IsDualConormalPrimitive X U b := by
  rw [ProductPrimitiveCriterion.normalizedDualProduct_iff_transitionPrimitive ℂ X U]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨dualConormalGaugeEquiv X U a, (dualConormalGaugeEquiv_primitive X U a).mp ha⟩
  · rintro ⟨b, hb⟩
    refine ⟨(dualConormalGaugeEquiv X U).symm b, (dualConormalGaugeEquiv_primitive X U _).mpr ?_⟩
    rwa [LinearEquiv.apply_symm_apply]

end

/-! Scalar primitives for the values on a basis reconstruct an
actual conormal-valued primitive and hence a normalized global product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] CommonOpenCocycle.dualFamilyPairAffineOpen ChartGauge.dualFamilyChartAffineOpen

variable (X : Over (Spec (.of (DualNumber ℂ)))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left]
    [Smooth (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] [GrpObj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)]
    (U : X.left.AffineOpenCover)

abbrev dualScalarGaugeParameters := ∀ i : U.I₀,
  HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (CommonOpenFiber.dualAffineCommonOpenFiber ℂ X (ChartGauge.dualFamilyChartAffineOpen ℂ X U i))

def IsDualScalarConormalPrimitive
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X))
    (a : dualScalarGaugeParameters X U) : Prop := ∀ i j : U.I₀,
  DualAffine.ConormalCocycle.dualFamilyPairConormalTransition X U i j z =
    CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap ℂ X
      (show (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j).1 ≤ (ChartGauge.dualFamilyChartAffineOpen ℂ X U i).1 from inf_le_left)
        (a i) -
    CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap ℂ X
      (show (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j).1 ≤ (ChartGauge.dualFamilyChartAffineOpen ℂ X U j).1 from inf_le_right)
        (a j)

theorem conormalPrimitive_iff_basisPrimitives {J : Type}
    (b : Module.Basis J ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X))) :
    (∃ v : dualConormalGaugeParameters X U, IsDualConormalPrimitive X U v) ↔
      ∀ t : J, ∃ a : dualScalarGaugeParameters X U, IsDualScalarConormalPrimitive X U (b t) a := by
  constructor
  · rintro ⟨v, hv⟩ t
    exact ⟨fun i => v i (b t), fun i j => hv i j (b t)⟩
  · intro h
    choose a ha using h
    let v : dualConormalGaugeParameters X U := fun i => b.constr ℂ (fun t => a t i)
    refine ⟨v, fun i j z => ?_⟩
    have hv : DualAffine.ConormalCocycle.dualFamilyPairConormalTransition X U i j =
        DualAffine.ConormalCoordinates.dualAffineConormalRestriction X
          (show (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j).1 ≤ (ChartGauge.dualFamilyChartAffineOpen ℂ X U i).1 from inf_le_left) (v i) -
        DualAffine.ConormalCoordinates.dualAffineConormalRestriction X
          (show (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j).1 ≤ (ChartGauge.dualFamilyChartAffineOpen ℂ X U j).1 from inf_le_right) (v j) := by
      apply b.ext
      intro t
      simp only [LinearMap.sub_apply, DualAffine.ConormalCoordinates.dualAffineConormalRestriction_apply, v, Module.Basis.constr_basis]
      exact ha t i j
    exact congrArg (fun f => f z) hv

theorem normalizedDualProduct_iff_basisPrimitives {J : Type}
    (b : Module.Basis J ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X))) :
    (∃ e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X),
      NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e) ↔
      ∀ t : J, ∃ a : dualScalarGaugeParameters X U, IsDualScalarConormalPrimitive X U (b t) a :=
  (normalizedDualProduct_iff_conormalPrimitive X U).trans (conormalPrimitive_iff_basisPrimitives X U b)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalBasisPrimitives
