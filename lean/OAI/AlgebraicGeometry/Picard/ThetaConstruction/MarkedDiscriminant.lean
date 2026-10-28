import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationTypeData
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualLe

/-! # Marked Discriminant -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual integral-dual discriminant is identified with the
cokernel of the fixed marked integer form, and hence its fixed type. -/

section
open OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationTypeData.Geometric

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} (T : DefinitionsIntegral.MarkedPolarizedTorus g E)

def DefinitionsIntegral.MarkedPolarizedTorus.markedDualEquiv : T.integralDualLattice ≃ₗ[ℤ] ((DefinitionsIntegral.Index g → ℤ) →ₗ[ℤ] ℤ) :=
  T.integralDualEquiv.trans (DefinitionsIntegral.Geometric.integralMarkingEquiv T).dualMap

theorem DefinitionsIntegral.MarkedPolarizedTorus.markedDualEquiv_inclusion (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice)
    (n : DefinitionsIntegral.Index g → ℤ) :
    T.markedDualEquiv (T.integralDualInclusion l) n =
      Matrix.toBilin' E ((DefinitionsIntegral.Geometric.integralMarkingEquiv T).symm l) n := by
  let n' : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice := DefinitionsIntegral.Geometric.integralMarkingEquiv T n
  calc
    T.markedDualEquiv (T.integralDualInclusion l) n =
        T.integralDualEquiv (T.integralDualInclusion l) n' := rfl
    _ = DefinitionsIntegral.Geometric.integralLatticeForm T l n' := T.integralDualEquiv_inclusion l n'
    _ = Matrix.toBilin' E ((DefinitionsIntegral.Geometric.integralMarkingEquiv T).symm l) n := by
      change Matrix.toBilin' E ((DefinitionsIntegral.Geometric.integralMarkingEquiv T).symm l)
        ((DefinitionsIntegral.Geometric.integralMarkingEquiv T).symm (DefinitionsIntegral.Geometric.integralMarkingEquiv T n)) = _
      exact congrArg (fun v => Matrix.toBilin' E ((DefinitionsIntegral.Geometric.integralMarkingEquiv T).symm l) v)
        ((DefinitionsIntegral.Geometric.integralMarkingEquiv T).symm_apply_apply n)

def DefinitionsIntegral.MarkedPolarizedTorus.markedDiscriminantEquiv :
    (T.integralDualLattice ⧸ T.integralDualInclusion.range) ≃ₗ[ℤ]
      (((DefinitionsIntegral.Index g → ℤ) →ₗ[ℤ] ℤ) ⧸ (Matrix.toBilin' E).range) :=
  Submodule.Quotient.equiv _ _ T.markedDualEquiv (by
    rw [← LinearMap.range_comp]
    ext f
    constructor
    · rintro ⟨l, rfl⟩
      refine ⟨(DefinitionsIntegral.Geometric.integralMarkingEquiv T).symm l, ?_⟩
      apply LinearMap.ext
      intro n
      exact (T.markedDualEquiv_inclusion l n).symm
    · rintro ⟨n, rfl⟩
      refine ⟨DefinitionsIntegral.Geometric.integralMarkingEquiv T n, ?_⟩
      apply LinearMap.ext
      intro m
      exact (T.markedDualEquiv_inclusion (DefinitionsIntegral.Geometric.integralMarkingEquiv T n) m).trans
        (congrArg (fun v => Matrix.toBilin' E v m) ((DefinitionsIntegral.Geometric.integralMarkingEquiv T).symm_apply_apply n)))

def DefinitionsIntegral.MarkedPolarizedTorus.discriminantTypeEquiv (D : PolarizationTypeData.Geometric.IntegralPolarizationType E) :
    (T.integralDualLattice ⧸ T.integralDualInclusion.range) ≃+
      ((∀ i : Fin g, ZMod (D.elementaryDivisors i)) ×
        (∀ i : Fin g, ZMod (D.elementaryDivisors i))) :=
  T.markedDiscriminantEquiv.toAddEquiv.trans D.cokernel

end

namespace MarkedDiscriminant.Geometric.MarkedPolarizedTorus

end MarkedDiscriminant.Geometric.MarkedPolarizedTorus

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
