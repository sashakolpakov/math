import OAI.AlgebraicGeometry.Divisors.LineBundles.ProductPeriodicComplex
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! # Product Equation Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProductEquationImage.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the actual image of multiplication on the product quotient

When a is nonzero in a domain, multiplication by a identifies R/(b)
with its image in R/(ab). Its module length is consequently the actual
order of b, without a numerical multiplicity hypothesis.
-/

variable {R : Type*} [CommRing R]

def productEquationImageProjection (a b : R) :
    R →ₗ[R] (MultiplicationSequence.BundleCycles.equationEndomorphism a (ProductPeriodicComplex.BundleCycles.productEquationQuotient a b)).range :=
  (MultiplicationSequence.BundleCycles.equationEndomorphism a (ProductPeriodicComplex.BundleCycles.productEquationQuotient a b)).rangeRestrict.comp (Ideal.span {a * b}).mkQ

theorem productEquationImageProjection_surjective (a b : R) :
    Function.Surjective (productEquationImageProjection a b) := by
  rintro ⟨_, q, rfl⟩
  obtain ⟨r, rfl⟩ := (Ideal.span {a * b}).mkQ_surjective q
  exact ⟨r, rfl⟩

theorem productEquationImageProjection_kernel [IsDomain R] (a b : R) (ha : a ≠ 0) :
    (productEquationImageProjection a b).ker = Ideal.span {b} := by
  ext r
  constructor
  · intro hr
    have hz : (Ideal.span {a * b}).mkQ (a * r) = 0 := congrArg Subtype.val hr
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero _).mp hz)
    exact Ideal.mem_span_singleton.mpr ⟨d, mul_left_cancel₀ ha (hd.trans (mul_assoc a b d))⟩
  · intro hr
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hr
    apply Subtype.ext
    change (Ideal.span {a * b}).mkQ (a * (b * d)) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Ideal.mem_span_singleton.mpr ⟨d, (mul_assoc a b d).symm⟩

def productEquationImageEquiv [IsDomain R] (a b : R) (ha : a ≠ 0) :
    (MultiplicationSequence.BundleCycles.equationEndomorphism a (ProductPeriodicComplex.BundleCycles.productEquationQuotient a b)).range ≃ₗ[R] R ⧸ Ideal.span {b} :=
  ((productEquationImageProjection a b).quotKerEquivOfSurjective
    (productEquationImageProjection_surjective a b)).symm.trans
      (Submodule.quotEquivOfEq _ _ (productEquationImageProjection_kernel a b ha))

theorem productEquationImage_length [IsDomain R] (a b : R) (ha : a ≠ 0) :
    Module.length R (MultiplicationSequence.BundleCycles.equationEndomorphism a (ProductPeriodicComplex.BundleCycles.productEquationQuotient a b)).range = Ring.ord R b :=
  (productEquationImageEquiv a b ha).length_eq

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProductEquationImage.BundleCycles
