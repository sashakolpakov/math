import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PrimitiveDual
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualIsogenyType
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel

/-! # Concrete Polarized Period Model -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Actual HilbertConstruction polarized abelian objects on the original algebraic
period model. The dual, positivity, finite-flat degree and geometric
kernel type all come from proved factories. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel T} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T}

section
variable {p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N} (C : PrimitiveDual.Geometric.PrimitiveDualConstruction p)

def PrimitiveDual.Geometric.PrimitiveDualConstruction.polarization (D : PolarizationTypeData.Geometric.IntegralPolarizationType E) : AbelianModuli.HilbertConstruction.PolarizationData.Polarization C.dual D.elementaryDivisors where
  isogeny := p.isogeny
  kernelType := p.hasPolarizationType D
  positive K _ _ z := C.positive K z

def PrimitiveDual.Geometric.PrimitiveDualConstruction.polarized (D : PolarizationTypeData.Geometric.IntegralPolarizationType E) {level : ℕ}
    (β : M.abelianScheme.FullLevel level) :
    AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g D.elementaryDivisors level Foundations.Scheme.ProjectiveSpace.complexBase where
  abelian := M.abelianScheme
  dual := C.dual
  polarization := C.polarization D
  level := β

end

def ConcretePolarizedPeriodModel.Geometric.actualPolarizedPeriodModel (M : PeriodModel.Geometric.AlgebraicPeriodModel T)
    (hE : E.transpose = -E) (hEdet : E.det ≠ 0) (level : ℕ) [NeZero level] :
    AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g (PolarizationTypeData.Geometric.integralPolarizationTypeData E hE hEdet).elementaryDivisors
      level Foundations.Scheme.ProjectiveSpace.complexBase := by
  let N := (PrimitiveDual.Geometric.exists_primitive_dual_on_actual_model M hE).choose
  let p := (PrimitiveDual.Geometric.exists_primitive_dual_on_actual_model M hE).choose_spec.choose
  let C : PrimitiveDual.Geometric.PrimitiveDualConstruction p :=
    Classical.choice (PrimitiveDual.Geometric.exists_primitive_dual_on_actual_model M hE).choose_spec.choose_spec
  exact C.polarized (PolarizationTypeData.Geometric.integralPolarizationTypeData E hE hEdet)
    (AbelianModuli.ReferenceFamily.Complex.ComplexLevel.fullLevel M.abelianScheme M.abelian.variety.presentation.projective level)

theorem ConcretePolarizedPeriodModel.Geometric.actualPolarizedPeriodModel_abelian (M : PeriodModel.Geometric.AlgebraicPeriodModel T)
    (hE : E.transpose = -E) (hEdet : E.det ≠ 0) (level : ℕ) [NeZero level] :
    (ConcretePolarizedPeriodModel.Geometric.actualPolarizedPeriodModel M hE hEdet level).abelian = M.abelianScheme := rfl

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
