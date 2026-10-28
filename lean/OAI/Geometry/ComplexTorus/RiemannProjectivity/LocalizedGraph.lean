import OAI.Geometry.ComplexTorus.RiemannProjectivity.GraphGermsOn
import OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothKernelQuotientLocal

/-! # Localized Graph -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalizedGraph.Constructions.LocalizedGraphGerms

noncomputable section

/-! # RiemannProjectivity: the regular branch gives a faithful smooth local algebra -/

open Set _root_.Polynomial
open OAI.Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SmoothEquationPoint OAI.Geometry.ComplexTorus.RiemannProjectivity.GraphGermsOn.Constructions.GraphGerms

variable {n m : ℕ}

abbrev smoothRing (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ)) :=
  Localization.Away (JacobianLocalizationAt.Constructions.SmoothEquationPoint.presentation F).jacobian

theorem jacobian_unit (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hzero : ∀ y ∈ U, ∀ j, (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0)
    (hderiv : ∀ j, ((F j).map (MvPolynomial.eval x)).derivative.eval (ψ x j) ≠ 0) :
    IsUnit (GraphGermsOn.Constructions.GraphGerms.equationMap F x ψ hU hx hψ hzero (JacobianLocalizationAt.Constructions.SmoothEquationPoint.presentation F).jacobian) := by
  apply (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.isUnit_iff_value_ne_zero x _).mpr
  have hv := congrArg (fun f : JacobianLocalizationAt.Constructions.SmoothEquationPoint.equationRing F →+* ℂ => f (JacobianLocalizationAt.Constructions.SmoothEquationPoint.presentation F).jacobian)
    (GraphGermsOn.Constructions.GraphGerms.equationMap_value F x ψ hU hx hψ hzero)
  change AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x (GraphGermsOn.Constructions.GraphGerms.equationMap F x ψ hU hx hψ hzero (JacobianLocalizationAt.Constructions.SmoothEquationPoint.presentation F).jacobian) = _ at hv
  rw [hv]
  change JacobianLocalizationAt.Constructions.SmoothEquationPoint.point F x (ψ x) (hzero x hx) (JacobianLocalizationAt.Constructions.SmoothEquationPoint.presentation F).jacobian ≠ 0
  rw [JacobianLocalizationAt.Constructions.SmoothEquationPoint.point_jacobian]
  exact JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.jacobian_det_ne_zero F x (ψ x) hderiv

def branchMap (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hzero : ∀ y ∈ U, ∀ j, (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0)
    (hderiv : ∀ j, ((F j).map (MvPolynomial.eval x)).derivative.eval (ψ x j) ≠ 0) :
    smoothRing F →ₐ[MvPolynomial (Fin n) ℂ] AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  IsLocalization.Away.liftAlgHom (f := GraphGermsOn.Constructions.GraphGerms.equationMap F x ψ hU hx hψ hzero)
    (JacobianLocalizationAt.Constructions.SmoothEquationPoint.presentation F).jacobian (jacobian_unit F x ψ hU hx hψ hzero hderiv)

def branchPoint (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hzero : ∀ y ∈ U, ∀ j, (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0)
    (hderiv : ∀ j, ((F j).map (MvPolynomial.eval x)).derivative.eval (ψ x j) ≠ 0) :
    smoothRing F →ₐ[ℂ] ℂ :=
  { (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x).comp (branchMap F x ψ hU hx hψ hzero hderiv).toRingHom with
    commutes' c := by
      rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin n) ℂ) (smoothRing F)]
      change AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x (branchMap F x ψ hU hx hψ hzero hderiv
        (algebraMap (MvPolynomial (Fin n) ℂ) (smoothRing F) (MvPolynomial.C c))) = c
      rw [(branchMap F x ψ hU hx hψ hzero hderiv).commutes]
      change MvPolynomial.eval x (MvPolynomial.C c) = c
      simp }

theorem exists_smooth_quotient_neighborhood
    (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ)) (hF : ∀ j, F j ≠ 0)
    (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hzero : ∀ y ∈ U, ∀ j, (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0)
    (hderiv : ∀ j, ((F j).map (MvPolynomial.eval x)).derivative.eval (ψ x j) ≠ 0)
    (I : Ideal (smoothRing F)) (hI : I.FG)
    (hvanish : I ≤ RingHom.ker (branchMap F x ψ hU hx hψ hzero hderiv).toRingHom) :
    ∃ s : smoothRing F,
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x (branchMap F x ψ hU hx hψ hzero hderiv s) ≠ 0 ∧
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk I s)) := by
  let : Algebra.IsAlgebraic (MvPolynomial (Fin n) ℂ) (JacobianLocalizationAt.Constructions.SmoothEquationPoint.equationRing F) :=
    EquationAlgebraicityIs.Constructions.EquationAlgebraicity.isAlgebraic F hF
  let : Algebra.IsAlgebraic (MvPolynomial (Fin n) ℂ) (smoothRing F) :=
    JacobianLocalizationAt.Constructions.AlgebraicLocalization.isAlgebraic (Submonoid.powers (JacobianLocalizationAt.Constructions.SmoothEquationPoint.presentation F).jacobian)
  let : Algebra.IsStandardSmooth ℂ (smoothRing F) :=
    JacobianLocalizationAt.Constructions.JacobianLocalization.isStandardSmooth (JacobianLocalizationAt.Constructions.SmoothEquationPoint.presentation F)
  let p := RingHom.ker ((AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x).comp
    (branchMap F x ψ hU hx hψ hzero hderiv).toRingHom)
  let : p.IsPrime := RingHom.ker_isPrime _
  have hp : RingHom.ker (branchMap F x ψ hU hx hψ hzero hderiv).toRingHom ≤ p := by
    intro a ha
    change AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x (branchMap F x ψ hU hx hψ hzero hderiv a) = 0
    rw [show branchMap F x ψ hU hx hψ hzero hderiv a = 0 from ha, map_zero]
  exact SmoothKernelQuotientLocal.Constructions.SmoothKernelQuotient.exists_smooth_neighborhood
    (branchMap F x ψ hU hx hψ hzero hderiv) (PolynomialHolomorphic.Constructions.PolynomialHolomorphicGerms.base_injective x)
    I hI hvanish p hp

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalizedGraph.Constructions.LocalizedGraphGerms
