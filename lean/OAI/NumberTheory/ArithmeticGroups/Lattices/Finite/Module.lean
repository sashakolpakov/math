import Mathlib

/-! # Module -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.Module.Construction

noncomputable section

/-! Finite congruence quotients of finitely generated integral modules. -/

open scoped Classical Pointwise

theorem finite_of_finitely_generated_torsion_by
    {R M : Type*} [CommRing R] [Ring.HasFiniteQuotients R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (d : R) (hd : d ≠ 0) (ht : Module.IsTorsionBy R M d) : Finite M := by
  let I : Ideal R := Ideal.span {d}
  have hI : I ≠ ⊥ := by simpa [I, Ideal.span_singleton_eq_bot] using hd
  let : Finite (R ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI
  have hset : Module.IsTorsionBySet R M I :=
    (Module.isTorsionBySet_span_singleton_iff d).mpr ht
  let : Module (R ⧸ I) M := hset.module
  let : IsScalarTower R (R ⧸ I) M := hset.isScalarTower
  let : Module.Finite (R ⧸ I) M := Module.Finite.of_restrictScalars_finite R (R ⧸ I) M
  exact Module.finite_of_finite (R ⧸ I)

theorem finite_quotient_element_smul
    {R M : Type*} [CommRing R] [Ring.HasFiniteQuotients R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (d : R) (hd : d ≠ 0) : Finite (M ⧸ d • (⊤ : Submodule R M)) :=
  finite_of_finitely_generated_torsion_by d hd (Module.isTorsionBy_quotient_element_smul M d)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.Module.Construction
