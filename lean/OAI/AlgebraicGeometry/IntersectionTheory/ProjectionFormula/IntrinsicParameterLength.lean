import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IsomorphismGermOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ParameterGerm
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricSupportLocalization

/-! # Intrinsic Parameter Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicParameterLength

noncomputable section

/-! The generic length of the native parameter quotient is the native
parameter order at the corresponding geometric point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

namespace Intrinsic

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem length (Z : Scheme) (A : IrreducibleCloseds Z) (t : Z ⟶ Spec (.of ℂ[X]))
    (x : Z) (hx : x ∈ (A : Set Z)) (a : ℂ) (p : PrimeSpectrum (Z.presheaf.stalk x))
    (hp : p ∈ Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hx)) :
    FiltrationBaseLength.length (Z.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
      (.of _ (QuotSMulTop (Affine.ParameterFiber.germ ℂ t x a) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hx))) =
      Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage A (Z.fromSpecStalk x p) (Local.SupportSpectrum.image_mem_support Z A x hx p hp)))
        (Local.Principal.supportStalkMap Z A (Z.fromSpecStalk x p)
          (Local.SupportSpectrum.image_mem_support Z A x hx p hp)
          (Affine.ParameterFiber.germ ℂ t (Z.fromSpecStalk x p) a)) := by
  let R := Z.presheaf.stalk x
  let r := Affine.ParameterFiber.germ ℂ t x a
  let q := Stalk.PrimeQuotient.kernelPrime Z A x hx
  let C := Affine.SupportStalk.support R q
  let i := Z.fromSpecStalk x
  have hqp := (GeometricSupportLocalization.Tor.support_iff Z A x hx p).mp hp
  have hC : i (CycleClass.Thom.IntersectionGeometry.supportPoint C) = CycleClass.Thom.IntersectionGeometry.supportPoint A := by
    rw [Affine.SupportStalk.point]
    exact Stalk.PrimeQuotient.kernelPrime_image Z A x hx
  let : IsIso (i.stalkMap p) := Stalk.Localization.stalkMap_isIso Z x p
  let e := QuotSMulTop.congr r (Stalk.PrimeQuotient.moduleEquiv Z A x hx q (Stalk.PrimeQuotient.kernelPrime_image Z A x hx))
  calc
    _ = FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal)
        (.of R (QuotSMulTop r (R ⧸ q.asIdeal))) :=
      FiltrationBaseLength.length_iso R (Localization.AtPrime p.asIdeal) e.toModuleIso
    _ = Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme C).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage C p (Affine.SupportStalk.mem R q p hqp)))
        (Local.Principal.supportStalkMap (Spec (.of R)) C p (Affine.SupportStalk.mem R q p hqp)
          (StructureSheaf.toStalk R p r)) := Affine.PrincipalBaseChange.SupportOrder.length R q p hqp r
    _ = _ := by
      change Ring.ord _ (Local.Principal.supportStalkMap (Spec (.of R)) C p (Affine.SupportStalk.mem R q p hqp)
        (StructureSheaf.toStalk R p (Affine.ParameterFiber.germ ℂ t x a))) = _
      rw [← Stalk.ParameterGerm.localization]
      exact Local.IsomorphismGermOrder.order i C A hC p (Affine.SupportStalk.mem R q p hqp)
        (Local.SupportSpectrum.image_mem_support Z A x hx p hp)
        (Affine.ParameterFiber.germ ℂ t (Z.fromSpecStalk x p) a)

theorem nonzero (Z : Scheme) (A : IrreducibleCloseds Z) (t : Z ⟶ Spec (.of ℂ[X]))
    (x : Z) (hx : x ∈ (A : Set Z)) (a : ℂ)
    (hr : Local.Principal.supportStalkMap Z A x hx (Affine.ParameterFiber.germ ℂ t x a) ≠ 0)
    (p : PrimeSpectrum (Z.presheaf.stalk x))
    (hp : p ∈ Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hx)) :
    Local.Principal.supportStalkMap Z A (Z.fromSpecStalk x p)
      (Local.SupportSpectrum.image_mem_support Z A x hx p hp)
      (Affine.ParameterFiber.germ ℂ t (Z.fromSpecStalk x p) a) ≠ 0 := by
  let R := Z.presheaf.stalk x
  let q := Stalk.PrimeQuotient.kernelPrime Z A x hx
  let C := Affine.SupportStalk.support R q
  let i := Z.fromSpecStalk x
  have hqp := (GeometricSupportLocalization.Tor.support_iff Z A x hx p).mp hp
  have hC : i (CycleClass.Thom.IntersectionGeometry.supportPoint C) = CycleClass.Thom.IntersectionGeometry.supportPoint A := by
    rw [Affine.SupportStalk.point]
    exact Stalk.PrimeQuotient.kernelPrime_image Z A x hx
  have hrq : Affine.ParameterFiber.germ ℂ t x a ∉ q.asIdeal := hr
  have h := Affine.PrincipalBaseChange.SupportOrder.image_ne_zero R q p hqp
    (Affine.ParameterFiber.germ ℂ t x a) hrq
  rw [← Stalk.ParameterGerm.localization] at h
  exact (Open.SupportGermOrder.nonzero_iff i C A hC p (Affine.SupportStalk.mem R q p hqp)
    (Local.SupportSpectrum.image_mem_support Z A x hx p hp)
    (Affine.ParameterFiber.germ ℂ t (Z.fromSpecStalk x p) a)).mp h

theorem weight (Z : Scheme) (A : IrreducibleCloseds Z) (t : Z ⟶ Spec (.of ℂ[X]))
    (x : Z) (hx : x ∈ (A : Set Z)) (a : ℂ) (p : PrimeSpectrum (Z.presheaf.stalk x))
    (hp : p ∈ Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hx))
    (hr : Local.Principal.supportStalkMap Z A x hx (Affine.ParameterFiber.germ ℂ t x a) ≠ 0) :
    ((FiltrationBaseLength.length (Z.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
      (.of _ (QuotSMulTop (Affine.ParameterFiber.germ ℂ t x a) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hx)))).toNat : ℚ) =
      GlobalParameterSum.Weights.weight Z (Z.fromSpecStalk x p)
        (Affine.ParameterFiber.germ ℂ t (Z.fromSpecStalk x p) a) A := by
  rw [GlobalParameterSum.Weights.weight,
    dite_eq_left (Local.SupportSpectrum.image_mem_support Z A x hx p hp),
    ite_eq_left (nonzero Z A t x hx a hr p hp), length Z A t x hx a p hp]

end Intrinsic

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicParameterLength
