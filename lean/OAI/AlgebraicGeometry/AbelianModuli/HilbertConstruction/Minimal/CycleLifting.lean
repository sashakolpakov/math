import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ResidueSections

/-! # Cycle Lifting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Lifting a residue-field degree-zero cocycle when the minimal first differential vanishes. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (ModuleCat.{u} R)} (P : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex S)

theorem Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.lift_residue_first_cycle (ht : P.complex.f.hom = 0)
    (z : IsLocalRing.ResidueField R ⊗[R] S.X₁)
    (hz : S.f.hom.baseChange (IsLocalRing.ResidueField R) z = 0) :
    ∃ x : S.X₁, S.f x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z := by
  let E := P.baseChangeFirstCyclesEquiv (IsLocalRing.ResidueField R)
  let z' : LinearMap.ker (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).f.hom := ⟨z, hz⟩
  have hsurj : Function.Surjective
      (TensorProduct.mk R (IsLocalRing.ResidueField R) P.complex.X₁ 1) :=
    TensorProduct.mk_surjective R P.complex.X₁ (IsLocalRing.ResidueField R)
      Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ := hsurj (E z').val
  refine ⟨P.equivalence.inv.τ₁ y, ?_, ?_⟩
  · have h := CategoryTheory.congr_fun P.equivalence.inv.comm₁₂ y
    change S.f (P.equivalence.inv.τ₁ y) = P.equivalence.inv.τ₂ (P.complex.f.hom y) at h
    rw [ht, LinearMap.zero_apply, map_zero] at h
    exact h
  · have hb := congrArg Subtype.val (E.symm_apply_apply z')
    change (P.equivalence.inv.τ₁.hom.baseChange (IsLocalRing.ResidueField R)) (E z').val = z at hb
    rw [← hy] at hb
    exact hb

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
