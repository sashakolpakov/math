import OAI.AlgebraicGeometry.Quotients.FiniteDescent.MinimalCycleLifting
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.MinimalCohomologyRigidity

/-! # Minimal Comparison -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.MinimalComparison.Construction.LocalSectionLifting

noncomputable section

/-! Transporting a cohomology-detecting comparison to minimal complexes and lifting fiber sections. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {S T : ShortComplex (ModuleCat.{u} R)}
    (P : LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex S) (Q : LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex T)

def localMinimalComparison (φ : S ⟶ T) : P.complex ⟶ Q.complex :=
  P.equivalence.inv ≫ φ ≫ Q.equivalence.hom

theorem localMinimalComparison_residue_homology_injective (φ : S ⟶ T)
    (hφ : Function.Injective (ShortComplex.homologyMap
      ((ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R (IsLocalRing.ResidueField R)).mapShortComplex.map φ))) :
    Function.Injective (ShortComplex.homologyMap
      ((ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R (IsLocalRing.ResidueField R)).mapShortComplex.map
        (localMinimalComparison P Q φ))) := by
  let F := ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R (IsLocalRing.ResidueField R)
  let H := F.mapShortComplex ⋙ ShortComplex.homologyFunctor (ModuleCat (IsLocalRing.ResidueField R))
  let eP : H.obj S ≅ H.obj P.complex := P.baseChangeHomologyIso (IsLocalRing.ResidueField R)
  let eQ : H.obj T ≅ H.obj Q.complex := Q.baseChangeHomologyIso (IsLocalRing.ResidueField R)
  have hm : Mono (H.map φ) := (ModuleCat.mono_iff_injective _).mpr hφ
  have he : H.map (localMinimalComparison P Q φ) = eP.inv ≫ H.map φ ≫ eQ.hom := by
    change H.map (P.equivalence.inv ≫ φ ≫ Q.equivalence.hom) = _
    rw [H.map_comp, H.map_comp]
    rfl
  apply (ModuleCat.mono_iff_injective (H.map (localMinimalComparison P Q φ))).mp
  rw [he]
  infer_instance

theorem localMinimalComparison_first_zero (φ : S ⟶ T) (hQ : Q.complex.f.hom = 0)
    (hφ : Function.Injective (ShortComplex.homologyMap
      ((ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R (IsLocalRing.ResidueField R)).mapShortComplex.map φ))) :
    P.complex.f.hom = 0 :=
  MinimalCohomologyRigidity.Construction.LocalSectionLifting.first_differential_eq_zero_of_residue_homology_injective (localMinimalComparison P Q φ)
    P.incoming_residue_zero P.outgoing_residue_zero Q.outgoing_residue_zero hQ
    (localMinimalComparison_residue_homology_injective P Q φ hφ)

include P in
theorem lift_residue_cycle_of_minimal_comparison (φ : S ⟶ T) (hQ : Q.complex.f.hom = 0)
    (hφ : Function.Injective (ShortComplex.homologyMap
      ((ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R (IsLocalRing.ResidueField R)).mapShortComplex.map φ)))
    (z : IsLocalRing.ResidueField R ⊗[R] S.X₁)
    (hz : S.f.hom.baseChange (IsLocalRing.ResidueField R) z = 0) :
    ∃ x : S.X₁, S.f x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z :=
  P.lift_residue_first_cycle (localMinimalComparison_first_zero P Q φ hQ hφ) z hz

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.MinimalComparison.Construction.LocalSectionLifting
