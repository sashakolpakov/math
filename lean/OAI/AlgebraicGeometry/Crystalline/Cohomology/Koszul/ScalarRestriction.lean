import OAI.NumberTheory.PadicHodge.PeriodInvariants.KoszulBaseChangeCoordinates
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Scalar Restriction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ScalarRestriction.KoszulScalarRestriction

noncomputable section

/-! # Changing the coordinate scalar ring in an actual Koszul complex -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.PeriodInvariants.KoszulSemilinearBaseChange OAI.NumberTheory.PadicHodge.PeriodInvariants.KoszulBaseChangeCoordinates
open OAI.NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCoordinates

universe u

variable (R S M σ : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [Fintype σ] [LinearOrder σ]

def coefficient : M →ₛₗ[algebraMap R S] M where
  toFun := id
  map_add' _ _ := rfl
  map_smul' r x := (IsScalarTower.algebraMap_smul S r x).symm

theorem term_bijective (n : ℕ) : Function.Bijective (NumberTheory.PadicHodge.PeriodInvariants.KoszulSemilinearBaseChange.termMap (σ := σ) (coefficient R S M) n) := by
  constructor
  · intro x y hxy
    apply (NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCoordinates.coordinates (M := M) (NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n)).injective
    have hx := NumberTheory.PadicHodge.PeriodInvariants.KoszulBaseChangeCoordinates.coordinates_commutes (coefficient R S M) n x
    have hy := NumberTheory.PadicHodge.PeriodInvariants.KoszulBaseChangeCoordinates.coordinates_commutes (coefficient R S M) n y
    exact hx.symm.trans ((congrArg (NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCoordinates.coordinates (M := M)
      (NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n)) hxy).trans hy)
  · exact NumberTheory.PadicHodge.PeriodInvariants.KoszulBaseChangeCoordinates.surjective (coefficient R S M) (fun x => ⟨x, rfl⟩) n

variable (D : σ → Module.End S M) (hD : ∀ i j, Function.Commute (D i) (D j))

def complexMap : Tensor.KoszulTensor.complex R σ M (fun i => (D i).restrictScalars R) hD ⟶
    NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex (algebraMap R S)
      (Tensor.KoszulTensor.complex S σ M D hD) :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap
    (NumberTheory.PadicHodge.PeriodInvariants.KoszulSemilinearBaseChange.complexMap (fun i => (D i).restrictScalars R) D
      (coefficient R S M) (fun _ _ => rfl) hD hD)

instance complexMap_isIso : IsIso (complexMap R S M σ D hD) := by
  have hc : ∀ n, IsIso ((complexMap R S M σ D hD).f n) := by
    intro n
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact term_bijective R S M σ n
  let := hc
  exact HomologicalComplex.Hom.isIso_of_components _

def complexIso : Tensor.KoszulTensor.complex R σ M (fun i => (D i).restrictScalars R) hD ≅
    NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex (algebraMap R S)
      (Tensor.KoszulTensor.complex S σ M D hD) := asIso (complexMap R S M σ D hD)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ScalarRestriction.KoszulScalarRestriction
