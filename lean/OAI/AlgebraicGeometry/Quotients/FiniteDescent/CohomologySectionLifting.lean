import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FreeSectionLifting
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ResidueCyclesNakayama

/-! # Cohomology Section Lifting -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent

noncomputable section

/-! A comparison with surjective degree-zero base change and injective first fiber cohomology
forces degree-zero base change to be surjective on the source. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {S T : ShortComplex (ModuleCat.{u} R)}

theorem LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex.first_zero_of_residue_cycles_lift (P : LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex S)
    (hS : ∀ (z : IsLocalRing.ResidueField R ⊗[R] S.X₁),
      S.f.hom.baseChange (IsLocalRing.ResidueField R) z = 0 →
      ∃ x : S.X₁, S.f x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z) :
    P.complex.f.hom = 0 := by
  apply ResidueCyclesNakayama.Construction.LocalSectionLifting.linearMap_eq_zero_of_residue_cycles_lift
  intro w
  let E := P.baseChangeFirstCyclesEquiv (IsLocalRing.ResidueField R)
  let w' : LinearMap.ker (ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) P.complex).f.hom :=
    ⟨w, by
      change P.complex.f.hom.baseChange (IsLocalRing.ResidueField R) w = 0
      rw [P.incoming_residue_zero, LinearMap.zero_apply]⟩
  let z' := E.symm w'
  obtain ⟨x, hx, hz⟩ := hS z'.val z'.property
  refine ⟨P.equivalence.hom.τ₁ x, ?_, ?_⟩
  · have h := CategoryTheory.congr_fun P.equivalence.hom.comm₁₂ x
    change P.complex.f.hom (P.equivalence.hom.τ₁ x) = P.equivalence.hom.τ₂ (S.f x) at h
    rw [hx, map_zero] at h
    exact h
  · have hb := congrArg Subtype.val (E.apply_symm_apply w')
    change (P.equivalence.hom.τ₁.hom.baseChange (IsLocalRing.ResidueField R)) z'.val = w at hb
    rw [← hz] at hb
    exact hb

theorem CohomologySectionLifting.Construction.LocalSectionLifting.finiteFree_cycle_lifting_of_cohomology_comparison
    (S T : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃]
    [Module.Finite R T.X₁] [Module.Free R T.X₁]
    [Module.Finite R T.X₂] [Module.Free R T.X₂]
    [Module.Finite R T.X₃] [Module.Free R T.X₃]
    (φ : S ⟶ T)
    (hT : ∀ (z : IsLocalRing.ResidueField R ⊗[R] T.X₁),
      T.f.hom.baseChange (IsLocalRing.ResidueField R) z = 0 →
      ∃ x : T.X₁, T.f x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z)
    (hφ : Function.Injective (ShortComplex.homologyMap
      ((ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R (IsLocalRing.ResidueField R)).mapShortComplex.map φ)))
    (z : IsLocalRing.ResidueField R ⊗[R] S.X₁)
    (hz : S.f.hom.baseChange (IsLocalRing.ResidueField R) z = 0) :
    ∃ x : S.X₁, S.f x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z := by
  obtain ⟨P⟩ := LocalMinimalShort.Construction.LocalSectionLifting.exists_localMinimalShortComplex S
  obtain ⟨Q⟩ := LocalMinimalShort.Construction.LocalSectionLifting.exists_localMinimalShortComplex T
  exact MinimalComparison.Construction.LocalSectionLifting.lift_residue_cycle_of_minimal_comparison P Q φ
    (Q.first_zero_of_residue_cycles_lift hT) hφ z hz

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent
