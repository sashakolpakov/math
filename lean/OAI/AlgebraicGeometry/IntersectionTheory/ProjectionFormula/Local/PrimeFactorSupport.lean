import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.CycleLocalOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeEquationOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoheightOneCodimension
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Prime Factor Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrimeFactorSupport

noncomputable section

/-! Each prime factor of an ambient local function defines an actual
codimension-one support, with coefficient one and its native restricted order. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

def prime (X : Scheme) (x : X) (r : X.presheaf.stalk x) (hr : Prime r) :
    PrimeSpectrum (X.presheaf.stalk x) :=
  ⟨Ideal.span {r}, (Ideal.span_singleton_prime hr.ne_zero).mpr hr⟩

theorem height (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (x : X.carrier)
    (r : X.carrier.presheaf.stalk x) (hr : Prime r) :
    (prime X.carrier x r hr).asIdeal.height = 1 := by
  let := X.stalk_isDomain x
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hr.ne_zero) hr.not_isUnit

def support (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (x : X.carrier)
    (r : X.carrier.presheaf.stalk x) (hr : Prime r) : X.DimensionCycleSupport 1 :=
  ⟨Stalk.DivisorSupport.primeClosure X.carrier x (prime X.carrier x r hr),
    CoheightOneCodimension.codimension X m _ (by
      rw [Stalk.DivisorSupport.primeClosure_point, ← Stalk.Localization.height_eq_coheight_image]
      exact PrimeFactorSupport.height X x r hr)⟩

theorem point_mem (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (x : X.carrier)
    (r : X.carrier.presheaf.stalk x) (hr : Prime r) :
    x ∈ ((support X m x r hr).val : Set X.carrier) :=
  Stalk.DivisorSupport.point_mem_primeClosure X.carrier x (prime X.carrier x r hr)

theorem equation (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (x : X.carrier)
    (r : X.carrier.presheaf.stalk x) (hr : Prime r) :
    RingHom.ker (Principal.supportStalkMap X.carrier (support X m x r hr).val x
      (point_mem X m x r hr)).hom = Ideal.span {r} :=
  Stalk.PrimeQuotient.kernel_eq X.carrier _ x _ (prime X.carrier x r hr)
    (Stalk.DivisorSupport.primeClosure_point X.carrier x (prime X.carrier x r hr)).symm

theorem geometric_order (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (x : X.carrier) (r : X.carrier.presheaf.stalk x) (hr : Prime r)
    (B : X.DimensionCycleSupport 1) (hxB : x ∈ (B.val : Set X.carrier)) :
    X.carrier.ord (algebraMap (X.carrier.presheaf.stalk x) X.carrier.functionField r)
      (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) = if B = support X m x r hr then 1 else 0 :=
  PrimeEquationOrder.geometric X m (support X m x r hr) B x (point_mem X m x r hr) hxB r hr.ne_zero
    (equation X m x r hr)

theorem multiplicity (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport q) (C : X.DimensionCycleSupport (q + 1))
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (r : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) (hr : Prime r)
    (hra : Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA r ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (support X m (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) r hr).val A.val C.val =
      ((Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA))
          (Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA r)).toNat : ℚ) :=
  PrincipalLeft.intersectionMultiplicity_eq_order X A.val _ C.val hxA
    (point_mem X m (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) r hr) r hr.ne_zero
    (equation X m (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) r hr) hra

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrimeFactorSupport
