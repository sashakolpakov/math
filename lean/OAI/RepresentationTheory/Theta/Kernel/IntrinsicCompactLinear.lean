import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterLinear

/-! # Intrinsic Compact Linear -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactLinear.Intrinsic

noncomputable section

/-! The actual multiplicity action is a continuous complex linear
equivalence, including its standard and dual components. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicMultiplicityPhase
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterLinear.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

def multiplicityLinear (U V : Fin A.places → Matrix (Fin 2) (Fin 2) ℂ) :
    Adelic.BallGeometryData.ComplexPhase A →ₗ[ℂ] Adelic.BallGeometryData.ComplexPhase A :=
  LinearMap.pi fun v =>
    (LinearMap.pi fun ij : Fin 3 × Fin 2 =>
      ∑ r, U v ij.2 r • IntrinsicParameterLinear.Intrinsic.standardCoordinate A v (ij.1,r)).prod
    (LinearMap.pi fun ij : Fin 3 × Fin 2 =>
      ∑ r, V v ij.2 r • IntrinsicParameterLinear.Intrinsic.dualCoordinate A v (ij.1,r))

theorem multiplicityLinear_apply (U V : Fin A.places → Matrix (Fin 2) (Fin 2) ℂ)
    (w : Adelic.BallGeometryData.ComplexPhase A) : multiplicityLinear A U V w = IntrinsicCompactOne.IntrinsicMultiplicityPhase.multiplicityPhase A U V w := by
  funext v
  apply Prod.ext <;> funext ij <;>
    simp [multiplicityLinear,IntrinsicCompactOne.IntrinsicMultiplicityPhase.multiplicityPhase,IntrinsicParameterLinear.Intrinsic.standardCoordinate,IntrinsicParameterLinear.Intrinsic.dualCoordinate,Matrix.mulVec,dotProduct]

def compactLinearEquiv (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) : Adelic.BallGeometryData.ComplexPhase A ≃ₗ[ℂ] Adelic.BallGeometryData.ComplexPhase A where
  toFun := IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase A p
  invFun := IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhaseInverse A p
  left_inv := IntrinsicCompactOne.IntrinsicMultiplicityPhase.compact_phase_left_inverse A p
  right_inv := IntrinsicCompactOne.IntrinsicMultiplicityPhase.compact_phase_right_inverse A p
  map_add' w t := by
    simpa only [IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase,multiplicityLinear_apply] using
      (multiplicityLinear A (fun v => (p.change v).val) (fun v => (p.change v).invᵀ)).map_add w t
  map_smul' c w := by
    simpa only [IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase,multiplicityLinear_apply,RingHom.id_apply] using
      (multiplicityLinear A (fun v => (p.change v).val) (fun v => (p.change v).invᵀ)).map_smul c w

def compactContinuousEquiv (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) : Adelic.BallGeometryData.ComplexPhase A ≃L[ℂ] Adelic.BallGeometryData.ComplexPhase A :=
  (compactLinearEquiv A p).toContinuousLinearEquiv

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactLinear.Intrinsic
