import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.AdicCompatible

/-! # Cochain Quotient Tower -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientTower.PrincipalCochainQuotient

noncomputable section

/-! Original coefficient-power cohomology transitions form a tower, including
the shifted successive convention used by bounded crystalline cohomology. -/

open _root_.CategoryTheory

universe u v
variable (R : Type u) [CommRing R] (C : CochainComplex (ModuleCat.{v} R) ℕ) (r : R)

theorem transition_refl (n : ℕ) : PrincipalCochainExact.PrincipalCochainQuotient.transition R C r n n le_rfl = 𝟙 (PrincipalCochainExact.PrincipalCochainQuotient.quotient R C r n) := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (IntegralComparison.Principal.PowerModuleSequence.submodule R (C.X a) r n).mkQ_surjective x
  rfl

theorem transition_comp (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) :
    PrincipalCochainExact.PrincipalCochainQuotient.transition R C r m l hml ≫ PrincipalCochainExact.PrincipalCochainQuotient.transition R C r n m hnm =
      PrincipalCochainExact.PrincipalCochainQuotient.transition R C r n l (hnm.trans hml) := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (IntegralComparison.Principal.PowerModuleSequence.submodule R (C.X a) r l).mkQ_surjective x
  rfl

theorem cohomologyTransition_refl (i n : ℕ) (x : CochainQuotientCohomology.PrincipalCochainQuotient.cohomology R C r n i) :
    CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i n n le_rfl x = x := by
  change HomologicalComplex.homologyMap (PrincipalCochainExact.PrincipalCochainQuotient.transition R C r n n le_rfl) i x = x
  rw [transition_refl, HomologicalComplex.homologyMap_id]
  rfl

theorem cohomologyTransition_comp (i n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l)
    (x : CochainQuotientCohomology.PrincipalCochainQuotient.cohomology R C r l i) :
    CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i n m hnm (CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i m l hml x) =
      CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i n l (hnm.trans hml) x := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f i)
    (transition_comp R C r n m l hnm hml)
  rw [HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h x

def shiftedCompatibleEquiv (i : ℕ) :
    AdicCohomology.AdicCohomologyLimit.compatible (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomology R C r n i) (CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i) ≃ₗ[R]
      LinearMap.ker (IntegralComparison.SequentialModuleDifference.difference R (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomology R C r (n + 1) i)
        (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i (n + 1) (n + 2) (by omega))) :=
  (AdicCompatible.AdicCompatibleSequences.shiftEquiv R (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomology R C r n i)
    (CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i) (cohomologyTransition_refl R C r i)
    (cohomologyTransition_comp R C r i)).trans
      (AdicCompatible.AdicCompatibleSequences.sequentialEquiv R (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomology R C r (n + 1) i)
        (fun n m h => CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R C r i (n + 1) (m + 1) (Nat.add_le_add_right h 1))
        (fun n => cohomologyTransition_refl R C r i (n + 1))
        (fun n m l hnm hml => cohomologyTransition_comp R C r i (n + 1) (m + 1) (l + 1)
          (Nat.add_le_add_right hnm 1) (Nat.add_le_add_right hml 1)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientTower.PrincipalCochainQuotient
