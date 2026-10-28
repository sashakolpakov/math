import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonB
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.TensorFiltration
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFiltrationConstruction
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ScalarExtension

/-! # Geometric Filtration -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.GeometricFiltration

noncomputable section

/-! Canonical period filtrations on crystalline invariants and their scalar extension. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.MaximalUnramified OAI.NumberTheory.PadicHodge.WeakAdmissibility.ValuationStructure OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonB
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisD OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Scalars OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Filtration OAI.NumberTheory.PadicHodge.WeakAdmissibility.TensorFiltration
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFiltrationConstruction OAI.NumberTheory.PadicHodge.WeakAdmissibility.ScalarExtension
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

def deRhamTensorStep (i : ℤ) : Submodule K (Logarithm.PeriodRings.BdR p ⊗[ℚ_[p]] V) :=
  TensorFiltration.scalarTensorStep (R := ℚ_[p]) (DeRhamField.Scalars.fieldFiltration p K) i

theorem deRhamTensorStep_antitone : Antitone (deRhamTensorStep p K (V := V)) :=
  TensorFiltration.tensorStep_antitone (fun i => (DeRhamField.Scalars.fieldFiltration p K i).restrictScalars ℚ_[p])
    (DeRhamField.Scalars.fieldFiltration_antitone p K)

theorem deRhamTensorStep_exhaustive (x : Logarithm.PeriodRings.BdR p ⊗[ℚ_[p]] V) :
    ∃ i : ℤ, x ∈ deRhamTensorStep p K i :=
  TensorFiltration.tensorStep_exhaustive (fun i => (DeRhamField.Scalars.fieldFiltration p K i).restrictScalars ℚ_[p])
    (DeRhamField.Scalars.fieldFiltration_antitone p K) (DeRhamField.Filtration.filtration_exhaustive p) x

theorem deRhamTensorStep_separated (x : Logarithm.PeriodRings.BdR p ⊗[ℚ_[p]] V)
    (hx : ∀ i : ℤ, x ∈ deRhamTensorStep p K i) : x = 0 :=
  TensorFiltration.tensorStep_separated (fun i => (DeRhamField.Scalars.fieldFiltration p K i).restrictScalars ℚ_[p])
    (DeRhamField.Filtration.filtration_separated p) x hx

variable [Module.Finite ℚ_[p] K] (ρ : Representation ℚ_[p] K.fixingSubgroup V)

instance invariantAddCommGroup : AddCommGroup (DcrisD.Dcris p K ρ) :=
  @Submodule.addCommGroup ℚ_[p] (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) _ _ _ (DcrisD.Dcris p K ρ)

def invariantStep (i : ℤ) : Submodule (MaximalUnramified.K0 p K) (DcrisD.Dcris p K ρ) :=
  (deRhamTensorStep p (MaximalUnramified.K0 p K) i).comap (ComparisonB.dCrisToDeRhamTensor p K ρ)

theorem invariantStep_antitone : Antitone (invariantStep p K ρ) := by
  intro i j hij x hx
  exact deRhamTensorStep_antitone p (MaximalUnramified.K0 p K) hij hx

theorem invariantStep_exhaustive (x : DcrisD.Dcris p K ρ) : ∃ i : ℤ, x ∈ invariantStep p K ρ i :=
  deRhamTensorStep_exhaustive p (MaximalUnramified.K0 p K) (ComparisonB.dCrisToDeRhamTensor p K ρ x)

theorem invariantStep_separated (x : DcrisD.Dcris p K ρ)
    (hx : ∀ i : ℤ, x ∈ invariantStep p K ρ i) : x = 0 := by
  exact ComparisonB.dCrisToDeRhamTensor_injective p K ρ
    ((deRhamTensorStep_separated p (MaximalUnramified.K0 p K) _ hx).trans
      (map_zero (ComparisonB.dCrisToDeRhamTensor p K ρ)).symm)

def invariantFiniteFiltration [Module.Finite (MaximalUnramified.K0 p K) (DcrisD.Dcris p K ρ)] :
    FilteredRepresentations.Construction.FiniteFiltration (MaximalUnramified.K0 p K) (DcrisD.Dcris p K ρ) :=
  FiniteFiltrationConstruction.ofExhaustiveSeparated (invariantStep p K ρ) (invariantStep_antitone p K ρ)
    (invariantStep_exhaustive p K ρ) (invariantStep_separated p K ρ)

def scalarComparison : K ⊗[MaximalUnramified.K0 p K] DcrisD.Dcris p K ρ →ₗ[K] (Logarithm.PeriodRings.BdR p ⊗[ℚ_[p]] V) :=
  ScalarExtension.extend (R := MaximalUnramified.K0 p K) (S := K) (ComparisonB.dCrisToDeRhamTensor p K ρ)

theorem scalarComparison_tmul (a : K) (x : DcrisD.Dcris p K ρ) :
    scalarComparison p K ρ (a ⊗ₜ[MaximalUnramified.K0 p K] x) = a • ComparisonB.dCrisToDeRhamTensor p K ρ x := rfl

/-- The filtration is pulled back from the actual de Rham tensor filtration. -/
def scalarStep (i : ℤ) : Submodule K (K ⊗[MaximalUnramified.K0 p K] DcrisD.Dcris p K ρ) :=
  (deRhamTensorStep p K i).comap (scalarComparison p K ρ)

theorem scalarStep_antitone : Antitone (scalarStep p K ρ) := by
  intro i j hij x hx
  exact deRhamTensorStep_antitone p K hij hx

theorem scalarStep_exhaustive (x : K ⊗[MaximalUnramified.K0 p K] DcrisD.Dcris p K ρ) :
    ∃ i : ℤ, x ∈ scalarStep p K ρ i :=
  deRhamTensorStep_exhaustive p K (scalarComparison p K ρ x)

theorem scalarStep_intersection (x : K ⊗[MaximalUnramified.K0 p K] DcrisD.Dcris p K ρ) :
    (∀ i : ℤ, x ∈ scalarStep p K ρ i) ↔ scalarComparison p K ρ x = 0 := by
  constructor
  · exact deRhamTensorStep_separated p K _
  · intro hx i
    change scalarComparison p K ρ x ∈ deRhamTensorStep p K i
    rw [hx]
    exact (deRhamTensorStep p K i).zero_mem

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.GeometricFiltration
