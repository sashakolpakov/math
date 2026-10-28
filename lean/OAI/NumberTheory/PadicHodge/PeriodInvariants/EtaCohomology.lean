import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaBoundaries

/-! # Eta Cohomology -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCohomology

noncomputable section

/-!
# Eta cohomology as a quotient by scalar torsion

In every positive degree, the map on cycles induces a surjection onto
eta cohomology. Its kernel is exactly the scalar-torsion submodule.
The cycle quotients here are connected to categorical homology separately.
-/

universe u v

open _root_.CategoryTheory OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaComplex OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCycles OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaBoundaries

variable {R : Type u} [CommRing R] (a : R)

def cohomology (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :=
  EtaCycles.cycles C (n + 1) ⧸ LinearMap.range (EtaBoundaries.toCycles C n)

def etaCohomology (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :=
  EtaCycles.etaCycles a C (n + 1) ⧸ LinearMap.range (EtaBoundaries.etaToCycles a C n)

instance cohomology_addCommGroup (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    AddCommGroup (cohomology C n) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance cohomology_module (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    Module R (cohomology C n) := inferInstanceAs (Module R (_ ⧸ _))

instance etaCohomology_addCommGroup (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    AddCommGroup (etaCohomology a C n) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance etaCohomology_module (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    Module R (etaCohomology a C n) := inferInstanceAs (Module R (_ ⧸ _))

def compare (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (ha : IsSMulRegular (C.X (n + 1)) a) : cohomology C n →ₗ[R] etaCohomology a C n :=
  (LinearMap.range (EtaBoundaries.toCycles C n)).mapQ (LinearMap.range (EtaBoundaries.etaToCycles a C n))
    (EtaCycles.scaleCycles a C (n + 1)) (EtaBoundaries.scaleCycles_preserves_boundaries a C n ha)

theorem compare_surjective (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (ha : IsSMulRegular (C.X (n + 1)) a) (ha' : IsSMulRegular (C.X (n + 1 + 1)) a) :
    Function.Surjective (compare a C n ha) := by
  intro x
  obtain ⟨z, rfl⟩ := (LinearMap.range (EtaBoundaries.etaToCycles a C n)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := EtaCycles.scaleCycles_surjective a C (n + 1) ha' z
  exact ⟨(LinearMap.range (EtaBoundaries.toCycles C n)).mkQ y, rfl⟩

theorem compare_eq_zero_iff (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (ha : IsSMulRegular (C.X (n + 1)) a) (x : cohomology C n) :
    compare a C n ha x = 0 ↔ a • x = 0 := by
  refine Submodule.Quotient.induction_on (LinearMap.range (EtaBoundaries.toCycles C n)) x ?_
  intro z
  change (Submodule.Quotient.mk (EtaCycles.scaleCycles a C (n + 1) z) : etaCohomology a C n) = 0 ↔
    (Submodule.Quotient.mk (a • z) : cohomology C n) = 0
  rw [Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
  exact EtaBoundaries.scaleCycles_mem_boundary_iff a C n ha z

def scalarTorsion (M : Type*) [AddCommGroup M] [Module R M] : Submodule R M :=
  LinearMap.ker (a • (LinearMap.id : M →ₗ[R] M))

theorem compare_ker (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (ha : IsSMulRegular (C.X (n + 1)) a) :
    LinearMap.ker (compare a C n ha) = scalarTorsion a (cohomology C n) := by
  ext x
  exact compare_eq_zero_iff a C n ha x

def quotientTorsionEquiv (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (ha : IsSMulRegular (C.X (n + 1)) a) (ha' : IsSMulRegular (C.X (n + 1 + 1)) a) :
    (cohomology C n ⧸ scalarTorsion a (cohomology C n)) ≃ₗ[R] etaCohomology a C n :=
  (Submodule.quotEquivOfEq _ _ (compare_ker a C n ha).symm).trans
    ((compare a C n ha).quotKerEquivOfSurjective (compare_surjective a C n ha ha'))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCohomology
