import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois

/-! # Dcris D -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisD

noncomputable section

/-!
The actual crystalline invariant space and its induced Frobenius.

For a subfield K of the fixed algebraic closure of ℚ_p, the fixing subgroup
is the actual G_K. These constructions also make sense without assuming
K/ℚ_p finite. The main WeakAdmissibility theorem must retain that finite-extension
hypothesis. The K₀-vector-space structure, finite-dimensionality, comparison
map, filtration, and weak admissibility are not assumed by this definition.
-/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois.PeriodStructure
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

def tensorRepresentation (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    Representation ℚ_[p] K.fixingSubgroup (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :=
  Representation.tprod ((Galois.PeriodStructure.periodRepresentation p).comp K.fixingSubgroup.subtype) ρ

/-- The underlying ℚ_p-vector space of D_cris, defined by actual Galois invariants. -/
def Dcris (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    Submodule ℚ_[p] (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) where
  carrier := {x | ∀ σ : K.fixingSubgroup, tensorRepresentation p K ρ σ x = x}
  zero_mem' σ := map_zero _
  add_mem' hx hy σ := by simp only [map_add, hx σ, hy σ]
  smul_mem' c x hx σ := by simp only [map_smulₛₗ, RingHom.id_apply, hx σ]

theorem mem_Dcris (ρ : Representation ℚ_[p] K.fixingSubgroup V) (x : Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :
    x ∈ Dcris p K ρ ↔ ∀ σ : K.fixingSubgroup, tensorRepresentation p K ρ σ x = x :=
  Iff.rfl

def tensorFrobenius : (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) →ₗ[ℚ_[p]] (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :=
  TensorProduct.map (Galois.PeriodStructure.bCrisFrobeniusAlg p).toLinearMap (LinearMap.id : V →ₗ[ℚ_[p]] V)

theorem tensorFrobenius_tmul (b : Logarithm.PeriodRings.BCris p) (v : V) :
    tensorFrobenius p (b ⊗ₜ[ℚ_[p]] v) = Galois.PeriodStructure.bCrisFrobeniusAlg p b ⊗ₜ[ℚ_[p]] v := by
  simp only [tensorFrobenius, TensorProduct.map_tmul, LinearMap.id_apply,
    AlgHom.toLinearMap_apply]

theorem tensorRepresentation_frobenius (ρ : Representation ℚ_[p] K.fixingSubgroup V)
    (σ : K.fixingSubgroup) (x : Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :
    tensorRepresentation p K ρ σ (tensorFrobenius p x) =
      tensorFrobenius p (tensorRepresentation p K ρ σ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    simp only [tensorRepresentation, Representation.tprod_apply, MonoidHom.comp_apply,
      tensorFrobenius_tmul, TensorProduct.map_tmul, Galois.PeriodStructure.periodRepresentation_frobenius]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorFrobenius_mem_Dcris (ρ : Representation ℚ_[p] K.fixingSubgroup V)
    {x : Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V} (hx : x ∈ Dcris p K ρ) :
    tensorFrobenius p x ∈ Dcris p K ρ := by
  change ∀ σ : K.fixingSubgroup, tensorRepresentation p K ρ σ x = x at hx
  change ∀ σ : K.fixingSubgroup,
    tensorRepresentation p K ρ σ (tensorFrobenius p x) = tensorFrobenius p x
  intro σ
  exact (tensorRepresentation_frobenius p K ρ σ x).trans
    (congrArg (tensorFrobenius p) (hx σ))

/-- The endomorphism induced by actual crystalline Frobenius on the invariant space. -/
def dCrisFrobenius (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    Dcris p K ρ →ₗ[ℚ_[p]] Dcris p K ρ :=
  LinearMap.codRestrict (Dcris p K ρ)
    ((tensorFrobenius p).comp (Dcris p K ρ).subtype)
    (fun x => tensorFrobenius_mem_Dcris p K ρ x.property)

theorem dCrisFrobenius_coe (ρ : Representation ℚ_[p] K.fixingSubgroup V) (x : Dcris p K ρ) :
    (dCrisFrobenius p K ρ x : Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) = tensorFrobenius p x := rfl

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisD
