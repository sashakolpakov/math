import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Exact
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Product Periodic Complex -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProductPeriodicComplex.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the exact multiplication complex on R/(ab)

For two nonzero elements in a domain, the kernel of multiplication by
either factor is the image of the other. This gives the exact periodic
complex used to compare all height-one branches of their product.
-/

variable {R : Type*} [CommRing R]

abbrev productEquationQuotient (a b : R) := R ⧸ Ideal.span ({a * b} : Set R)

theorem productEquation_comp_zero (a b : R) :
    (MultiplicationSequence.BundleCycles.equationEndomorphism b (productEquationQuotient a b)).comp
      (MultiplicationSequence.BundleCycles.equationEndomorphism a (productEquationQuotient a b)) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (Ideal.span ({a * b} : Set R)) (b * (a * c)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  exact ⟨c, by ring⟩

theorem productEquation_comp_zero_reverse (a b : R) :
    (MultiplicationSequence.BundleCycles.equationEndomorphism a (productEquationQuotient a b)).comp
      (MultiplicationSequence.BundleCycles.equationEndomorphism b (productEquationQuotient a b)) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (Ideal.span ({a * b} : Set R)) (a * (b * c)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  exact ⟨c, by ring⟩

def productPeriodicComplex (a b : R) :
    HomologicalComplex (ModuleCat R) Periodic.PeriodicComplex.BundleCycles.periodicComplexShape :=
  Periodic.PeriodicComplex.BundleCycles.endomorphismPeriodicComplex
    (MultiplicationSequence.BundleCycles.equationEndomorphism a (productEquationQuotient a b))
    (MultiplicationSequence.BundleCycles.equationEndomorphism b (productEquationQuotient a b))
    (productEquation_comp_zero a b) (productEquation_comp_zero_reverse a b)

variable [IsDomain R]

theorem productEquation_exact (a b : R) (hb : b ≠ 0) :
    Function.Exact (MultiplicationSequence.BundleCycles.equationEndomorphism a (productEquationQuotient a b))
      (MultiplicationSequence.BundleCycles.equationEndomorphism b (productEquationQuotient a b)) := by
  intro x
  constructor
  · obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    intro hx
    change Ideal.Quotient.mk (Ideal.span ({a * b} : Set R)) (b * c) = 0 at hx
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
    have hc : c = a * d := mul_left_cancel₀ hb (hd.trans (by ring))
    refine ⟨Ideal.Quotient.mk _ d, ?_⟩
    change Ideal.Quotient.mk _ (a * d) = Ideal.Quotient.mk _ c
    exact congrArg (Ideal.Quotient.mk _) hc.symm
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (productEquation_comp_zero a b) y

theorem productEquation_exact_reverse (a b : R) (ha : a ≠ 0) :
    Function.Exact (MultiplicationSequence.BundleCycles.equationEndomorphism b (productEquationQuotient a b))
      (MultiplicationSequence.BundleCycles.equationEndomorphism a (productEquationQuotient a b)) := by
  intro x
  constructor
  · obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    intro hx
    change Ideal.Quotient.mk (Ideal.span ({a * b} : Set R)) (a * c) = 0 at hx
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
    have hc : c = b * d := mul_left_cancel₀ ha (hd.trans (mul_assoc a b d))
    refine ⟨Ideal.Quotient.mk _ d, ?_⟩
    change Ideal.Quotient.mk _ (b * d) = Ideal.Quotient.mk _ c
    exact congrArg (Ideal.Quotient.mk _) hc.symm
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (productEquation_comp_zero_reverse a b) y

theorem productPeriodicComplex_homology_length_zero
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (i : Bool) :
    Module.length R ((productPeriodicComplex a b).homology i) = 0 :=
  Periodic.Exact.BundleCycles.endomorphismPeriodicComplex_homology_length_zero_of_exact _ _ _ _
    (productEquation_exact a b hb) (productEquation_exact_reverse a b ha) i

theorem productPeriodicEulerLength_zero
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : Module.length R ((productPeriodicComplex a b).homology false) ≠ ⊤)
    (h₁ : Module.length R ((productPeriodicComplex a b).homology true) ≠ ⊤) :
    Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (productPeriodicComplex a b) h₀ h₁ = 0 :=
  Periodic.Exact.BundleCycles.endomorphismPeriodicEulerLength_zero_of_exact _ _ _ _
    (productEquation_exact a b hb) (productEquation_exact_reverse a b ha) h₀ h₁

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProductPeriodicComplex.BundleCycles
