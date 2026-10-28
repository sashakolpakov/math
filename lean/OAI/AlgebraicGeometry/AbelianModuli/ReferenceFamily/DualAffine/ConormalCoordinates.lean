import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ConormalInclusions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenConormalLinearity

/-! # Conormal Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ConormalCoordinates

noncomputable section

section

/-! The actual affine derivation presheaf of a varying family is
identified with regular functions valued in the dual of the constructed
identity conormal module of its special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (X : Over (Spec (.of (DualNumber ℂ))))

variable [IsIntegral (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left] [Smooth (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] [GrpObj (ConormalInclusions.dualFamilySpecialFiberObject ℂ X)]

def dualAffineConormalLinearEquiv (V : X.left.affineOpens) :
    Derivation ℂ (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X V))
        (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X V)) ≃ₗ[ℂ]
      (Constructed.IdentityConormal.constructedIdentityConormal ℂ (ConormalInclusions.dualFamilySpecialFiberObject ℂ X) →ₗ[ℂ] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X V)) :=
  (Affine.OpenConormalLinearity.affineOpenConormalLinearEquiv (ConormalInclusions.dualFamilySpecialFiberObject ℂ X) (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X V)
    (ConormalInclusions.dualAffineCommonOpenInclusion ℂ X V)).restrictScalars ℂ

theorem dualAffineConormalLinearEquiv_natural {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (d : Derivation ℂ (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X W))
      (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X W))) (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) :
    dualAffineConormalLinearEquiv X V (Dual.CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction ℂ X h d) z =
      Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap ℂ X h (dualAffineConormalLinearEquiv X W d z) :=
  Affine.OpenConormalCoordinates.affineOpenConormalEquiv_natural ℂ (ConormalInclusions.dualFamilySpecialFiberObject ℂ X) (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X W)
    (ConormalInclusions.dualAffineCommonOpenInclusion ℂ X W) (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X V)
    (ConormalInclusions.dualAffineCommonOpenInclusion ℂ X V) (Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenMap ℂ X h)
    (ConormalInclusions.dualAffineCommonOpenInclusion_natural ℂ X h) (Dual.CommonOpenDerivationExtension.dualAffineCommonOpenAlgebraMap_etale ℂ X h) d z

end

/-! The affine derivation presheaf is naturally isomorphic to the
presheaf of linear functionals on the fixed identity conormal module,
with the literal regular-function restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (X : Over (Spec (.of (DualNumber ℂ))))
variable [IsIntegral (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left] [Smooth (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] [GrpObj (ConormalInclusions.dualFamilySpecialFiberObject ℂ X)]

def dualAffineConormalRestriction {V W : X.left.affineOpens} (h : V.1 ≤ W.1) :
    (Constructed.IdentityConormal.constructedIdentityConormal ℂ (ConormalInclusions.dualFamilySpecialFiberObject ℂ X) →ₗ[ℂ] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X W)) →ₗ[ℂ]
      (Constructed.IdentityConormal.constructedIdentityConormal ℂ (ConormalInclusions.dualFamilySpecialFiberObject ℂ X) →ₗ[ℂ] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X V)) :=
  LinearMap.llcomp ℂ _ _ _ (Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap ℂ X h).toLinearMap

omit [IsIntegral (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left] [Smooth (ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] in
theorem dualAffineConormalRestriction_apply {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (v : Constructed.IdentityConormal.constructedIdentityConormal ℂ (ConormalInclusions.dualFamilySpecialFiberObject ℂ X) →ₗ[ℂ] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X W))
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) :
    dualAffineConormalRestriction X h v z = Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap ℂ X h (v z) := rfl

def dualAffineConormalPresheaf : X.left.affineOpensᵒᵖ ⥤ ModuleCat ℂ where
  obj V := ModuleCat.of ℂ
    (Constructed.IdentityConormal.constructedIdentityConormal ℂ (ConormalInclusions.dualFamilySpecialFiberObject ℂ X) →ₗ[ℂ] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ (Dual.CommonOpenFiber.dualAffineCommonOpenFiber ℂ X V.unop))
  map f := ModuleCat.ofHom (dualAffineConormalRestriction X f.unop.le)
  map_id V := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro z
    exact congrArg (fun q => q (v z)) (Dual.AffineDerivationPresheaf.dualAffineCommonOpenAlgebraMap_id ℂ X V.unop)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro z
    exact congrArg (fun q => q (v z))
      (Dual.AffineDerivationPresheaf.dualAffineCommonOpenAlgebraMap_comp ℂ X g.unop.le f.unop.le)

theorem dualAffineConormalLinearEquiv_restriction {V W : X.left.affineOpens} (h : V.1 ≤ W.1) :
    (dualAffineConormalLinearEquiv X V).toLinearMap.comp (Dual.CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction ℂ X h) =
      (dualAffineConormalRestriction X h).comp (dualAffineConormalLinearEquiv X W).toLinearMap := by
  apply LinearMap.ext
  intro d
  apply LinearMap.ext
  intro z
  exact dualAffineConormalLinearEquiv_natural X h d z

def dualAffineConormalPresheafIso : Dual.AffineDerivationPresheaf.dualAffineDerivationPresheaf ℂ X ≅ dualAffineConormalPresheaf X :=
  NatIso.ofComponents (fun V => (dualAffineConormalLinearEquiv X V.unop).toModuleIso) (fun f =>
    ModuleCat.hom_ext (dualAffineConormalLinearEquiv_restriction X f.unop.le))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ConormalCoordinates
