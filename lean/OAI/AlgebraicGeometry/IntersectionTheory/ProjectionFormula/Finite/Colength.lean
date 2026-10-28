import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Length
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Localization.Integer

/-! # Colength -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Colength

noncomputable section

/-!
# ProjectionFormula: finite colength of finite birational extensions in dimension one

Denominators in the common fraction field make the cokernel torsion.
Finite generation gives a common nonzero annihilator, whose quotient ring
has dimension zero. This discharges the finite-colength condition used in
the normalization-length comparison.
-/

open scoped nonZeroDivisors

theorem length_ne_top_of_finite_torsion
    (R M : Type*) [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ht : Module.IsTorsion R M) : Module.length R M ≠ ⊤ := by
  obtain ⟨a, ha, hane⟩ := Submodule.annihilator_top_inter_nonZeroDivisors ht
  have hkill : Module.IsTorsionBy R M a := fun x =>
    Submodule.mem_annihilator.mp ha x (Submodule.mem_top)
  have hI : Module.IsTorsionBySet R M (Ideal.span {a}) :=
    (Module.isTorsionBySet_span_singleton_iff a).mpr hkill
  let : Module (R ⧸ Ideal.span {a}) M := hI.module
  let : IsScalarTower R (R ⧸ Ideal.span {a}) M := hI.isScalarTower
  have hlen := isFiniteLength_quotient_span_singleton R hane
  obtain ⟨hnoeth, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hlen
  let : IsArtinian R (R ⧸ Ideal.span {a}) := hart
  let : IsArtinianRing (R ⧸ Ideal.span {a}) := isArtinian_of_tower R inferInstance
  let : Module.Finite (R ⧸ Ideal.span {a}) M :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {a}) M
  rw [Module.length_eq_of_surjective (R := R ⧸ Ideal.span {a}) (S := R)
    (M := M) (Ideal.Quotient.mk_surjective)]
  exact Module.length_ne_top

theorem birational_quotient_isTorsion
    (R S K : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Field K]
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K] :
    Module.IsTorsion R (S ⧸ (Algebra.linearMap R S).range) := by
  intro x
  obtain ⟨s, rfl⟩ := (Algebra.linearMap R S).range.mkQ_surjective x
  obtain ⟨a, b, hb⟩ := IsLocalization.exists_integer_multiple R⁰ (algebraMap S K s)
  refine ⟨a, ?_⟩
  change (a : R) • (Submodule.Quotient.mk s : S ⧸ (Algebra.linearMap R S).range) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨b, ?_⟩
  apply IsFractionRing.injective S K
  change algebraMap S K (algebraMap R S b) =
    algebraMap S K ((a : R) • s)
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]
  simpa only [Algebra.smul_def] using hb

/-- A finite extension inside the same fraction field has finite colength
over a one-dimensional Noetherian domain. -/
theorem length_birational_quotient_ne_top
    (R S K : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Field K]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Algebra R S] [Module.Finite R S]
    [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K] :
    Module.length R (S ⧸ (Algebra.linearMap R S).range) ≠ ⊤ :=
  length_ne_top_of_finite_torsion R _ (birational_quotient_isTorsion R S K)

/-- The normalization-length comparison with finite colength discharged by
the actual common fraction field and module finiteness. -/
theorem ord_eq_length_birational_extension
    (R S K : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Field K]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Algebra R S] [Module.Finite R S]
    [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K]
    (a : R) (ha : a ≠ 0) :
    Ring.ord R a = Module.length R (S ⧸ Ideal.span {algebraMap R S a}) := by
  have hi : Function.Injective (algebraMap R S) := by
    apply Function.Injective.of_comp (f := algebraMap S K)
    simpa only [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq] using
      IsFractionRing.injective R K
  exact Normalization.Length.ord_eq_length_extension hi
    (length_birational_quotient_ne_top R S K) a ((map_ne_zero_iff _ hi).mpr ha)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Colength
