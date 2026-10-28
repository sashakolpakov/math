import OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeFiltrationMultiplicity

/-! # Whole Filtration -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-!
# LineBundleCycles: prime-filtration formulas on the full module

The quotient by the zero submodule is identified with the original module
by the first isomorphism theorem for its identity map. This transports
the proved filtration formulas to the full module without changing the
chosen factors.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def WholeFiltration.BundleCycles.quotientBottomEquiv : (M ⧸ (⊥ : Submodule R M)) ≃ₗ[R] M :=
  (Submodule.quotEquivOfEq _ _ LinearMap.ker_id.symm).trans
    ((LinearMap.id : M →ₗ[R] M).quotKerEquivOfSurjective Function.surjective_id)

theorem PrimeFiltration.BundleCycles.PrimeFiltrationAbove.whole_localized_length_eq_count (b : R) (hb : Module.IsTorsionBy R M b)
    (P : Ideal R) [P.IsPrime] (hP : P ∈ (Ideal.span {b}).minimalPrimes)
    (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove (⊥ : Submodule R M)) :
    Module.length (Localization P.primeCompl) (LocalizedModule P.primeCompl M) =
      (F.factors.count P : ℕ∞) :=
  (LocalizedFiltrationLength.BundleCycles.localizedModuleEquiv P.primeCompl (WholeFiltration.BundleCycles.quotientBottomEquiv (R := R) (M := M))).length_eq.symm.trans
    (F.localized_length_eq_count b hb P hP)

variable [IsNoetherianRing R] [Module.Finite R M]

theorem PrimeFiltration.BundleCycles.PrimeFiltrationAbove.whole_eulerSum_eq (a b : R) (hI : IsFiniteLength R (R ⧸ Ideal.span {a, b}))
    (hb : Module.IsTorsionBy R M b) (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove (⊥ : Submodule R M)) :
    F.eulerSum a b hI hb = EquationFiniteLength.BundleCycles.twoEquationEulerLength a b hI hb :=
  (F.eulerSum_eq a b hI hb).trans
    (TwoEquationEulerFunctorial.BundleCycles.twoEquationEulerLength_equiv a b hI WholeFiltration.BundleCycles.quotientBottomEquiv (hb.quotient ⊥) hb)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
