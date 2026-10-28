import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationFiniteLength
import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationEulerEquiv

/-! # Two Equation Euler Functorial -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.TwoEquationEulerFunctorial.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual finite two-equation invariants on subquotients

An annihilating equation stays zero on submodules and quotients.
The proved finite-length criteria therefore apply throughout a prime
filtration. The resulting numerical invariant respects actual module
isomorphisms and the actual submodule/quotient exact sequence.
-/

variable {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]

omit [IsNoetherianRing R] in
theorem equationAnnihilator_submodule (b : R) (hb : Module.IsTorsionBy R M b) (P : Submodule R M) :
    Module.IsTorsionBy R P b := fun {x} => Subtype.ext (@hb x.1)

variable [Module.Finite R M] (a b : R) (hI : IsFiniteLength R (R ⧸ Ideal.span {a, b}))

theorem twoEquationEulerLength_additive (hb : Module.IsTorsionBy R M b) (P : Submodule R M) :
    EquationFiniteLength.BundleCycles.twoEquationEulerLength a b hI hb =
      EquationFiniteLength.BundleCycles.twoEquationEulerLength a b hI (equationAnnihilator_submodule b hb P) +
        EquationFiniteLength.BundleCycles.twoEquationEulerLength a b hI (hb.quotient P) :=
  EquationEulerLength.BundleCycles.equationEulerLength_additive a P
    (EquationFiniteLength.BundleCycles.equationKernel_finite_of_two_equations a b hI (equationAnnihilator_submodule b hb P))
    (EquationFiniteLength.BundleCycles.equationCokernel_finite_of_two_equations a b hI (equationAnnihilator_submodule b hb P))
    (EquationFiniteLength.BundleCycles.equationKernel_finite_of_two_equations a b hI hb)
    (EquationFiniteLength.BundleCycles.equationCokernel_finite_of_two_equations a b hI hb)
    (EquationFiniteLength.BundleCycles.equationKernel_finite_of_two_equations a b hI (hb.quotient P))
    (EquationFiniteLength.BundleCycles.equationCokernel_finite_of_two_equations a b hI (hb.quotient P))

theorem twoEquationEulerLength_equiv {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : M ≃ₗ[R] N) (hbM : Module.IsTorsionBy R M b) (hbN : Module.IsTorsionBy R N b) :
    EquationFiniteLength.BundleCycles.twoEquationEulerLength a b hI hbM = EquationFiniteLength.BundleCycles.twoEquationEulerLength a b hI hbN :=
  EquationEulerEquiv.BundleCycles.equationEulerLength_equiv a e
    (EquationFiniteLength.BundleCycles.equationKernel_finite_of_two_equations a b hI hbM)
    (EquationFiniteLength.BundleCycles.equationCokernel_finite_of_two_equations a b hI hbM)
    (EquationFiniteLength.BundleCycles.equationKernel_finite_of_two_equations a b hI hbN)
    (EquationFiniteLength.BundleCycles.equationCokernel_finite_of_two_equations a b hI hbN)

theorem twoEquationEulerLength_zero_of_finite (hb : Module.IsTorsionBy R M b) (hM : Module.length R M ≠ ⊤) :
    EquationFiniteLength.BundleCycles.twoEquationEulerLength a b hI hb = 0 :=
  EquationEulerLength.BundleCycles.equationEulerLength_zero_of_finite a M
    (EquationFiniteLength.BundleCycles.equationKernel_finite_of_two_equations a b hI hb)
    (EquationFiniteLength.BundleCycles.equationCokernel_finite_of_two_equations a b hI hb) hM

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.TwoEquationEulerFunctorial.BundleCycles
