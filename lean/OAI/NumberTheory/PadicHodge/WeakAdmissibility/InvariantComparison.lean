import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonScalars
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisD

/-! # Invariant Comparison -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.InvariantComparison

noncomputable section

/-!
The comparison on the actual invariant tensor spaces. The K/K_0 scalar
identifications and finite filtered-module theorem are separate constructions.
-/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois.PeriodStructure OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonScalars OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisD
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

def deRhamTensorRepresentation (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    Representation ℚ_[p] K.fixingSubgroup (Logarithm.PeriodRings.BdR p ⊗[ℚ_[p]] V) :=
  Representation.tprod ((ComparisonScalars.deRhamRepresentation p).comp K.fixingSubgroup.subtype) ρ

/-- De Rham invariants for the genuine action of G_K. -/
def DdeRham (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    Submodule ℚ_[p] (Logarithm.PeriodRings.BdR p ⊗[ℚ_[p]] V) where
  carrier := {x | ∀ σ : K.fixingSubgroup, deRhamTensorRepresentation p K ρ σ x = x}
  zero_mem' σ := map_zero _
  add_mem' hx hy σ := by simp only [map_add, hx σ, hy σ]
  smul_mem' c x hx σ := by simp only [map_smulₛₗ, RingHom.id_apply, hx σ]

def tensorComparison : (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) →ₗ[ℚ_[p]] (Logarithm.PeriodRings.BdR p ⊗[ℚ_[p]] V) :=
  TensorProduct.map (ComparisonScalars.bCrisToBdRAlg p).toLinearMap (LinearMap.id : V →ₗ[ℚ_[p]] V)

theorem tensorComparison_tmul (b : Logarithm.PeriodRings.BCris p) (v : V) :
    tensorComparison p (b ⊗ₜ[ℚ_[p]] v) = ComparisonScalars.bCrisToBdRAlg p b ⊗ₜ[ℚ_[p]] v := by
  simp only [tensorComparison, TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply]

theorem tensorComparison_galois (ρ : Representation ℚ_[p] K.fixingSubgroup V)
    (σ : K.fixingSubgroup) (x : Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :
    tensorComparison p (DcrisD.tensorRepresentation p K ρ σ x) =
      deRhamTensorRepresentation p K ρ σ (tensorComparison p x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    simp only [DcrisD.tensorRepresentation, deRhamTensorRepresentation, Representation.tprod_apply,
      MonoidHom.comp_apply, TensorProduct.map_tmul, tensorComparison_tmul]
    exact congrArg (fun z : Logarithm.PeriodRings.BdR p => z ⊗ₜ[ℚ_[p]] ρ σ v) (ComparisonScalars.comparison_linear_galois p σ.val b)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorComparison_mem_DdeRham (ρ : Representation ℚ_[p] K.fixingSubgroup V)
    {x : Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V} (hx : x ∈ DcrisD.Dcris p K ρ) :
    tensorComparison p x ∈ DdeRham p K ρ := by
  change ∀ σ : K.fixingSubgroup, DcrisD.tensorRepresentation p K ρ σ x = x at hx
  change ∀ σ : K.fixingSubgroup,
    deRhamTensorRepresentation p K ρ σ (tensorComparison p x) = tensorComparison p x
  intro σ
  exact (tensorComparison_galois p K ρ σ x).symm.trans (congrArg (tensorComparison p) (hx σ))

/-- The constructed map on invariants, with no comparison-isomorphism hypothesis. -/
def invariantComparison (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    DcrisD.Dcris p K ρ →ₗ[ℚ_[p]] DdeRham p K ρ :=
  LinearMap.codRestrict (DdeRham p K ρ)
    ((tensorComparison p).comp (DcrisD.Dcris p K ρ).subtype)
    (fun x => tensorComparison_mem_DdeRham p K ρ x.property)

theorem invariantComparison_coe (ρ : Representation ℚ_[p] K.fixingSubgroup V) (x : DcrisD.Dcris p K ρ) :
    (invariantComparison p K ρ x : Logarithm.PeriodRings.BdR p ⊗[ℚ_[p]] V) = tensorComparison p x := rfl

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.InvariantComparison
