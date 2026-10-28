import OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalCochainExact
import OAI.NumberTheory.PadicHodge.GeometricComparison.AdicCohomology

/-! # Cochain Quotient Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient

noncomputable section

/-! Exact coefficient-power cohomology maps and the completion comparison for an actual regular cochain complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable (R : Type u) [CommRing R] (C : CochainComplex (ModuleCat.{v} R) ℕ) (r : R)
  (hreg : ∀ a, IsSMulRegular (C.X a) r)

abbrev cohomology (n i : ℕ) := (PrincipalCochainExact.PrincipalCochainQuotient.quotient R C r n).homology i

def reduction (n i : ℕ) : C.homology i →ₗ[R] cohomology R C r n i :=
  (HomologicalComplex.homologyMap (PrincipalCochainExact.PrincipalCochainQuotient.projection R C r n) i).hom

def cohomologyTransition (i n m : ℕ) (h : n ≤ m) :
    cohomology R C r m i →ₗ[R] cohomology R C r n i :=
  (HomologicalComplex.homologyMap (PrincipalCochainExact.PrincipalCochainQuotient.transition R C r n m h) i).hom

theorem reduction_transition (i n m : ℕ) (h : n ≤ m) (x : C.homology i) :
    cohomologyTransition R C r i n m h (reduction R C r m i x) = reduction R C r n i x := by
  have he := congrArg (fun f => HomologicalComplex.homologyMap f i) (PrincipalCochainExact.PrincipalCochainQuotient.projection_transition R C r n m h)
  rw [HomologicalComplex.homologyMap_comp] at he
  exact ConcreteCategory.congr_hom he x

include hreg in
theorem reduction_ker (n i : ℕ) : (reduction R C r n i).ker =
    IntegralComparison.Principal.PowerModuleSequence.submodule R (C.homology i) r n := by
  have he := (PrincipalCochainExact.PrincipalCochainQuotient.shortExact R C r hreg n).homology_exact₂ i |>.moduleCat_range_eq_ker
  change (HomologicalComplex.homologyMap (r ^ n • 𝟙 C) i).hom.range = (reduction R C r n i).ker at he
  rw [PrincipalCochainExact.PrincipalCochainQuotient.homology_scalar] at he
  rw [← he]
  ext x
  exact (IntegralComparison.Principal.PowerModuleSequence.mem_submodule R (C.homology i) r n x).symm

def quotientInclusion (n i : ℕ) :
    IntegralComparison.Principal.PowerModuleSequence.Quotient R (C.homology i) r n →ₗ[R] cohomology R C r n i :=
  (IntegralComparison.Principal.PowerModuleSequence.submodule R (C.homology i) r n).liftQ
    (reduction R C r n i) (reduction_ker R C r hreg n i).ge

theorem quotientInclusion_mk (n i : ℕ) (x : C.homology i) :
    quotientInclusion R C r hreg n i (Submodule.Quotient.mk x) = reduction R C r n i x := rfl

theorem quotientInclusion_injective (n i : ℕ) : Function.Injective (quotientInclusion R C r hreg n i) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (reduction_ker R C r hreg n i).le)

theorem connecting_ker (n i : ℕ) : (PrincipalCochainExact.PrincipalCochainQuotient.connecting R C r hreg n i).ker =
    (quotientInclusion R C r hreg n i).range := by
  rw [quotientInclusion, Submodule.range_liftQ]
  exact ((PrincipalCochainExact.PrincipalCochainQuotient.shortExact R C r hreg n).homology_exact₃ i (i + 1) rfl).moduleCat_range_eq_ker.symm

theorem quotientInclusion_transition (i n m : ℕ) (h : n ≤ m)
    (x : IntegralComparison.Principal.PowerModuleSequence.Quotient R (C.homology i) r m) :
    cohomologyTransition R C r i n m h (quotientInclusion R C r hreg m i x) =
      quotientInclusion R C r hreg n i (AdicCompletion.transitionMap (Ideal.span {r}) (C.homology i) h x) := by
  obtain ⟨y, rfl⟩ := (IntegralComparison.Principal.PowerModuleSequence.submodule R (C.homology i) r m).mkQ_surjective x
  exact reduction_transition R C r i n m h y

variable (i : ℕ) [IsNoetherian R (C.homology (i + 1))]

def completionEquiv : AdicCompletion (Ideal.span {r}) (C.homology i) ≃ₗ[R]
    AdicCohomology.AdicCohomologyLimit.compatible (fun n => cohomology R C r n i) (cohomologyTransition R C r i) :=
  AdicCohomology.AdicCohomologyLimit.equiv (Ideal.span {r}) r (fun n => cohomology R C r n i)
    (cohomologyTransition R C r i) (fun n => quotientInclusion R C r hreg n i)
    (fun n => PrincipalCochainExact.PrincipalCochainQuotient.connecting R C r hreg n i)
    (fun n => quotientInclusion_injective R C r hreg n i)
    (fun n => connecting_ker R C r hreg n i)
    (quotientInclusion_transition R C r hreg i)
    (fun n => PrincipalCochainExact.PrincipalCochainQuotient.connecting_transition R C r hreg n i)
    (fun n x => ⟨n, PrincipalCochainExact.PrincipalCochainQuotient.connecting_torsion R C r hreg n i x⟩)

theorem completionEquiv_of (x : C.homology i) (n : ℕ) :
    (completionEquiv R C r hreg i (AdicCompletion.of (Ideal.span {r}) (C.homology i) x)).val n =
      reduction R C r n i x := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient
