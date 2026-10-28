import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.CoefficientCechComparison
import Mathlib.Algebra.Algebra.Tower

/-! # Coefficient Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.CoefficientComposition

noncomputable section

/-! Composition of affine test-scheme maps gives the actual scalar tower on their coordinate rings. The coefficient functions on the pulled-back families satisfy the same geometric square. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {B C : Type u} [CommRing B] [CommRing C]

def specCoordinateRingMap (a : Spec (.of C) ⟶ Spec (.of B)) : B →+* C :=
  (CoefficientCechComparison.specBaseCoefficientMap a).comp (Scheme.ΓSpecIso (.of B)).inv.hom

theorem specCoordinateRingMap_comp
    (a : Spec (.of C) ⟶ Spec (.of B)) (g : Spec (.of B) ⟶ S) :
    (specCoordinateRingMap a).comp (CoefficientCechComparison.specBaseCoefficientMap g) = CoefficientCechComparison.specBaseCoefficientMap (a ≫ g) := by
  ext x
  change (Scheme.ΓSpecIso (.of C)).hom
      (a.appTop ((Scheme.ΓSpecIso (.of B)).inv ((Scheme.ΓSpecIso (.of B)).hom (g.appTop x)))) =
    (Scheme.ΓSpecIso (.of C)).hom ((a ≫ g).appTop x)
  exact congrArg (fun z : Γ(Spec (.of B), ⊤) => (Scheme.ΓSpecIso (.of C)).hom (a.appTop z))
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of B)).hom_inv_id (g.appTop x))

theorem specCoefficient_isScalarTower
    (a : Spec (.of C) ⟶ Spec (.of B)) (g : Spec (.of B) ⟶ S) :
    letI : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra
    letI : Algebra B C := (specCoordinateRingMap a).toAlgebra
    letI : Algebra Γ(S, ⊤) C := (CoefficientCechComparison.specBaseCoefficientMap (a ≫ g)).toAlgebra
    IsScalarTower Γ(S, ⊤) B C := by
  let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra
  let : Algebra B C := (specCoordinateRingMap a).toAlgebra
  let : Algebra Γ(S, ⊤) C := (CoefficientCechComparison.specBaseCoefficientMap (a ≫ g)).toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (specCoordinateRingMap_comp a g).symm

theorem specCoordinateRingMap_coefficients (a : Spec (.of C) ⟶ Spec (.of B)) :
    (Scheme.ΓSpecIso (.of C)).inv.hom.comp (specCoordinateRingMap a) =
      a.appTop.hom.comp (Scheme.ΓSpecIso (.of B)).inv.hom := by
  ext x
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of C)).hom_inv_id
    (a.appTop ((Scheme.ΓSpecIso (.of B)).inv x))

theorem specPullbackCoefficient_refinement
    {X Y : Scheme.{u}} (σ : X ⟶ Y) (b : Y ⟶ Spec (.of B)) (c : X ⟶ Spec (.of C))
    (a : Spec (.of C) ⟶ Spec (.of B)) (h : σ ≫ b = c ≫ a) :
    (CoefficientCechComparison.specPullbackCoefficientMap (b := c)).comp (specCoordinateRingMap a) =
      σ.appTop.hom.comp (CoefficientCechComparison.specPullbackCoefficientMap (b := b)) := by
  ext x
  exact (congrArg c.appTop (DFunLike.congr_fun (specCoordinateRingMap_coefficients a) x)).trans
    (congrArg (fun v : X ⟶ Spec (.of B) => v.appTop ((Scheme.ΓSpecIso (.of B)).inv x)) h).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.CoefficientComposition
