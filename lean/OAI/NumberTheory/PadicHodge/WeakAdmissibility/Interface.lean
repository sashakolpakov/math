import OAI.NumberTheory.PadicHodge.WeakAdmissibility.GeometricFiltration
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ValuationStructure

/-! # Interface -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.Interface

noncomputable section

/-!
Actual interfaces for the WeakAdmissibility statement. A finite extension is realized as a
subfield of the fixed algebraic closure of Q_p. The realization theorem below
shows that this convention includes every abstract finite extension.

Crystallinity is solely the dimension equality for actual Galois invariants.
No comparison isomorphism, invertibility, filtration bound, or admissibility
property is included in the definition.
-/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.MaximalUnramified OAI.NumberTheory.PadicHodge.WeakAdmissibility.ValuationStructure OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonB
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisD OAI.NumberTheory.PadicHodge.WeakAdmissibility.GeometricFiltration OAI.NumberTheory.PadicHodge.WeakAdmissibility.FilteredRepresentations.Construction
open scoped TensorProduct

def extendToAlgebra {R S D M : Type*} [Field R] [Semiring S] [Algebra R S]
    [AddCommMonoid D] [Module R D] [AddCommMonoid M] [Module R M] [Module S M]
    [IsScalarTower R S M] (f : D →ₗ[R] M) : S ⊗[R] D →ₗ[S] M :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a =>
        { toFun := fun d => a • f d
          map_add' := fun x y => by rw [map_add, smul_add]
          map_smul' := fun c d => by
            change a • f (c • d) = c • (a • f d)
            rw [map_smul, smul_comm] }
      map_add' := fun a b => LinearMap.ext fun d => add_smul a b (f d)
      map_smul' := fun a b => LinearMap.ext fun d => mul_smul a b (f d) }

variable (p : ℕ) [Fact p.Prime]

theorem finiteExtension_realization (L : Type*) [Field L] [Algebra ℚ_[p] L]
    [Module.Finite ℚ_[p] L] :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), Nonempty (L ≃ₐ[ℚ_[p]] K) := by
  let f : L →ₐ[ℚ_[p]] PadicAlgCl p := IsAlgClosed.lift
  exact ⟨f.fieldRange, ⟨f.equivFieldRange⟩⟩

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- A finite continuous Q_p-representation of the genuine fixing subgroup G_K. -/
structure FinitePadicGaloisRep where
  dimension : ℕ
  rho : Representation ℚ_[p] K.fixingSubgroup (Fin dimension → ℚ_[p])
  continuous_action : Continuous
    (fun x : K.fixingSubgroup × (Fin dimension → ℚ_[p]) => rho x.1 x.2)

variable [Module.Finite ℚ_[p] K]

namespace FinitePadicGaloisRep
variable (ρ : FinitePadicGaloisRep p K)

/-- The existing Galois-invariant tensor space, with its constructed K0 action. -/
abbrev crystallineInvariants := DcrisD.Dcris p K ρ.rho

/-- Cardinal dimension avoids the convention that finrank is zero in infinite dimension. -/
def IsCrystalline : Prop :=
  Module.rank (MaximalUnramified.K0 p K) (crystallineInvariants p K ρ) = (ρ.dimension : Cardinal)

theorem crystalline_finite (hρ : ρ.IsCrystalline p K) :
    Module.Finite (MaximalUnramified.K0 p K) (crystallineInvariants p K ρ) :=
  Module.finite_of_rank_eq_nat hρ

theorem crystalline_finrank (hρ : ρ.IsCrystalline p K) :
    Module.finrank (MaximalUnramified.K0 p K) (crystallineInvariants p K ρ) = ρ.dimension :=
  Module.finrank_eq_of_rank_eq hρ

end FinitePadicGaloisRep

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- The actual crystalline comparison b tensor d maps to b times d. -/
def crystallineComparison (ρ : Representation ℚ_[p] K.fixingSubgroup V) :
    Logarithm.PeriodRings.BCris p ⊗[MaximalUnramified.K0 p K] DcrisD.Dcris p K ρ →ₗ[Logarithm.PeriodRings.BCris p] (Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) :=
  extendToAlgebra (R := MaximalUnramified.K0 p K) (S := Logarithm.PeriodRings.BCris p) (ComparisonB.dCrisK0Subtype p K ρ)

theorem crystallineComparison_tmul (ρ : Representation ℚ_[p] K.fixingSubgroup V)
    (b : Logarithm.PeriodRings.BCris p) (x : DcrisD.Dcris p K ρ) :
    crystallineComparison p K ρ (b ⊗ₜ[MaximalUnramified.K0 p K] x) = b • (x : Logarithm.PeriodRings.BCris p ⊗[ℚ_[p]] V) := rfl

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.Interface
