import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.Comparison

/-! # Free Section Lifting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeSectionLifting.LocalSectionLifting

noncomputable section

/-! The finite-free-complex section lifting criterion used in local line-bundle triviality. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem exists_localMinimalShortComplex_of_first_zero (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃]
    (hf : S.f.hom = 0) :
    ∃ P : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex S, P.complex.f.hom = 0 := by
  obtain ⟨Q⟩ := Local.DifferentialNormalForm.LocalSectionLifting.exists_localMinimalDifferential S.X₂ S.X₃ S.g.hom
  let T := Local.OutgoingReduction.LocalSectionLifting.localOutgoingReducedComplex S Q
  have hTf : T.f.hom = 0 := by
    change (LinearMap.fst R Q.source Q.cancelled).comp
      (Q.sourceEquiv.symm.toLinearMap.comp S.f.hom) = 0
    rw [hf, LinearMap.comp_zero, LinearMap.comp_zero]
  let P : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex S := {
    complex := T
    firstFinite := ‹Module.Finite R S.X₁›
    firstFree := ‹Module.Free R S.X₁›
    middleFinite := Q.sourceFinite
    middleFree := Q.sourceFree
    lastFinite := Q.targetFinite
    lastFree := Q.targetFree
    equivalence := Local.OutgoingReduction.LocalSectionLifting.localOutgoingReduction S Q
    hom_h₀ := Local.OutgoingReduction.LocalSectionLifting.localOutgoingReduction_hom_h₀ S Q
    inv_h₀ := Local.OutgoingReduction.LocalSectionLifting.localOutgoingReduction_inv_h₀ S Q
    incoming_residue_zero := by rw [hTf, LinearMap.baseChange_zero]
    outgoing_residue_zero := Local.OutgoingReduction.LocalSectionLifting.localOutgoingReduced_residue_zero S Q }
  exact ⟨P, hTf⟩

theorem finiteFree_lift_residue_cycle_of_cohomology_injective
    (S T : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃]
    [Module.Finite R T.X₁] [Module.Free R T.X₁]
    [Module.Finite R T.X₂] [Module.Free R T.X₂]
    [Module.Finite R T.X₃] [Module.Free R T.X₃]
    (φ : S ⟶ T) (hT : T.f.hom = 0)
    (hφ : Function.Injective (ShortComplex.homologyMap
      ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (IsLocalRing.ResidueField R)).mapShortComplex.map φ)))
    (z : IsLocalRing.ResidueField R ⊗[R] S.X₁)
    (hz : S.f.hom.baseChange (IsLocalRing.ResidueField R) z = 0) :
    ∃ x : S.X₁, S.f x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z := by
  obtain ⟨P⟩ := Local.MinimalShortComplex.LocalSectionLifting.exists_localMinimalShortComplex S
  obtain ⟨Q, hQ⟩ := exists_localMinimalShortComplex_of_first_zero T hT
  exact Minimal.Comparison.LocalSectionLifting.lift_residue_cycle_of_minimal_comparison P Q φ hQ hφ z hz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeSectionLifting.LocalSectionLifting
