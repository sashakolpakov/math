import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CoefficientScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ComplexConstants
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CechCoefficient

/-! # Scalar Coefficient Snd -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ScalarCoefficientSnd

noncomputable section

/-! First-order scalar pullback on the actual overlap coefficients
uses restriction of the original global complex scalar section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]

theorem dualOpenSectionCoefficient_scalar_snd (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (hU : IsAffineOpen U) (c : ℂ) (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, U)) :
    (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU (DualOpen.Scalars.dualOpenScalarSection X U c s)).snd =
      X.left.presheaf.map (homOfLE (show (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        (Open.ComplexConstants.complexGlobalSectionMap X c) * (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU s).snd := by
  let : IsAffine (DualOpen.Product.dualReducedOpenOver X U).left := ReductionOpens.dualAffineOpen_reduction X U hU
  have h := congrArg TrivSqZeroExt.snd (DualOpen.CoefficientScalars.dualOpenSectionCoefficientEquiv_scalar X U hU c s)
  have hc := Open.ComplexConstants.openComplexConstant_global X ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U)
    (ReductionOpens.dualAffineOpen_reduction X U hU) c
  exact h.trans ((CoefficientScalars.dualCoefficientScale_snd _ _).trans
    (congrArg (fun a => a * (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU s).snd) hc))

theorem dualCechSectionCoefficient_scalar_snd
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    {I : Type} (U : I → (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : ∀ i, IsAffineOpen (U i))
    {n : ℕ} (a : Fin (n + 1) → I) (c : ℂ)
    (s : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) :
    (CechCoefficient.dualCechSectionCoefficientEquiv X U hU a (DualOpen.Scalars.dualOpenScalarSection X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) c s)).snd =
      X.left.presheaf.map (homOfLE (show AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechCoefficient.dualReducedCechCover X U) a ≤ ⊤ from le_top)).op
        (Open.ComplexConstants.complexGlobalSectionMap X c) * (CechCoefficient.dualCechSectionCoefficientEquiv X U hU a s).snd := by
  change Regular.SectionTransport.regularSectionTransport (CechCoefficient.dualReducedCechIntersection X U a)
    (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (CechCoefficient.dualCechIntersection_affine X U hU a)
      (DualOpen.Scalars.dualOpenScalarSection X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) c s)).snd = _
  rw [dualOpenSectionCoefficient_scalar_snd X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
    (CechCoefficient.dualCechIntersection_affine X U hU a) c s, map_mul]
  exact congrArg (fun r => r * (CechCoefficient.dualCechSectionCoefficientEquiv X U hU a s).snd)
    (Regular.SectionTransport.regularSectionTransport_restrict rfl (CechCoefficient.dualReducedCechIntersection X U a) le_top le_top
      (Open.ComplexConstants.complexGlobalSectionMap X c))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ScalarCoefficientSnd
