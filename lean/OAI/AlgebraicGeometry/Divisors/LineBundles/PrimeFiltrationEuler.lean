import OAI.AlgebraicGeometry.Divisors.LineBundles.TwoEquationEulerFunctorial
import OAI.AlgebraicGeometry.Divisors.LineBundles.SubquotientImage

/-! # Prime Filtration Euler -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-!
# LineBundleCycles: reduction of local intersection lengths to prime factors

The finite multiplication Euler length is the sum of the Euler lengths
of the actual prime cyclic factors of a constructed filtration. Every
factor is proved to be annihilated by the second equation, so finiteness
follows from the two-equation ideal rather than being stipulated factor
by factor.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem PrimeFiltrationEuler.BundleCycles.equationAnnihilator_equiv {N : Type*} [AddCommGroup N] [Module R N]
    (b : R) (e : M ≃ₗ[R] N) (hb : Module.IsTorsionBy R M b) :
    Module.IsTorsionBy R N b := by
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact (e.map_smul b y).symm.trans ((congrArg e (@hb y)).trans e.map_zero)

theorem PrimeFiltrationEuler.BundleCycles.primeFactor_annihilated (b : R) (hb : Module.IsTorsionBy R M b)
    (N L : Submodule R M) (J : Ideal R) (e : (L ⧸ N.comap L.subtype) ≃ₗ[R] R ⧸ J) :
    Module.IsTorsionBy R (R ⧸ J) b :=
  PrimeFiltrationEuler.BundleCycles.equationAnnihilator_equiv b e ((TwoEquationEulerFunctorial.BundleCycles.equationAnnihilator_submodule b hb L).quotient _)

variable [IsNoetherianRing R] [Module.Finite R M]
variable (a b : R) (hI : IsFiniteLength R (R ⧸ Ideal.span {a, b}))
variable (hb : Module.IsTorsionBy R M b)

/-- Sum over the actual prime cyclic factors, with finiteness derived for each factor. -/
def PrimeFiltration.BundleCycles.PrimeFiltrationAbove.eulerSum {N : Submodule R M} : PrimeFiltration.BundleCycles.PrimeFiltrationAbove N → ℤ
  | .top => 0
  | .step N L _ J _ e tail =>
      EquationFiniteLength.BundleCycles.twoEquationEulerLength a b hI (PrimeFiltrationEuler.BundleCycles.primeFactor_annihilated b hb N L J e) +
        eulerSum tail

/-- Additivity applied to every actual successive quotient of the filtration. -/
theorem PrimeFiltration.BundleCycles.PrimeFiltrationAbove.eulerSum_eq {N : Submodule R M} (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove N) :
    F.eulerSum a b hI hb = EquationFiniteLength.BundleCycles.twoEquationEulerLength a b hI (hb.quotient N) := by
  induction F with
  | top =>
    exact (TwoEquationEulerFunctorial.BundleCycles.twoEquationEulerLength_zero_of_finite a b hI (hb.quotient ⊤)
      (by rw [Module.length_eq_zero]; exact ENat.zero_ne_top)).symm
  | step N L hNL J hJ e tail ih =>
    let P := L.map N.mkQ
    have he := TwoEquationEulerFunctorial.BundleCycles.twoEquationEulerLength_equiv a b hI
      ((SubquotientImage.BundleCycles.subquotientImageEquiv N L).symm.trans e)
      (TwoEquationEulerFunctorial.BundleCycles.equationAnnihilator_submodule b (hb.quotient N) P)
      (PrimeFiltrationEuler.BundleCycles.primeFactor_annihilated b hb N L J e)
    have hq := TwoEquationEulerFunctorial.BundleCycles.twoEquationEulerLength_equiv a b hI
      (Submodule.quotientQuotientEquivQuotient N L hNL.le)
      ((hb.quotient N).quotient P) (hb.quotient L)
    change EquationFiniteLength.BundleCycles.twoEquationEulerLength a b hI (PrimeFiltrationEuler.BundleCycles.primeFactor_annihilated b hb N L J e) +
      tail.eulerSum a b hI hb = _
    rw [ih, ← he, ← hq]
    exact (TwoEquationEulerFunctorial.BundleCycles.twoEquationEulerLength_additive a b hI (hb.quotient N) P).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
