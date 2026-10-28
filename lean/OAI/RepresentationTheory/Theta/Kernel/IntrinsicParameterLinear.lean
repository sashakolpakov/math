import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector

/-! # Intrinsic Parameter Linear -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterLinear.Intrinsic

noncomputable section

/-! Linear maps underlying the explicit compact-place projector
matrices, and their exact action on the native reference graph. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

def standardCoordinate (v : Fin A.places) (ij : Fin 3 × Fin 2) : Adelic.BallGeometryData.ComplexPhase A →ₗ[ℂ] ℂ where
  toFun w := (w v).1 ij
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dualCoordinate (v : Fin A.places) (ij : Fin 3 × Fin 2) : Adelic.BallGeometryData.ComplexPhase A →ₗ[ℂ] ℂ where
  toFun w := (w v).2 ij
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ambientLinear (p : IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A) (z : IntrinsicExterior.Intrinsic.Tangent) : Adelic.BallGeometryData.ComplexPhase A →ₗ[ℂ] Adelic.BallGeometryData.ComplexPhase A :=
  LinearMap.pi fun v =>
    (LinearMap.pi fun ij : Fin 3 × Fin 2 =>
      if v = A.distinguished then
        Adelic.DeterminantCoordinates.lineVector z ij.1 • standardCoordinate A v (2,ij.2)
      else ∑ r, (p v).1 ij.2 r • standardCoordinate A v (ij.1,r)).prod
    (LinearMap.pi fun ij : Fin 3 × Fin 2 =>
      if v = A.distinguished then
        Adelic.DeterminantCoordinates.annihilatorVector z 0 ij.1 • dualCoordinate A v (0,ij.2) +
          Adelic.DeterminantCoordinates.annihilatorVector z 1 ij.1 • dualCoordinate A v (1,ij.2)
      else ∑ r, (p v).2 ij.2 r • dualCoordinate A v (ij.1,r))

theorem ambientLinear_apply (p : IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A) (z : IntrinsicExterior.Intrinsic.Tangent) (w : Adelic.BallGeometryData.ComplexPhase A) :
    ambientLinear A p z w = IntrinsicCompactProjector.IntrinsicParameter.ambientParameter A p z w := by
  funext v
  by_cases hv : v = A.distinguished
  all_goals
    apply Prod.ext
    all_goals
      funext ij
      simp [ambientLinear,IntrinsicCompactProjector.IntrinsicParameter.ambientParameter,standardCoordinate,dualCoordinate,hv]

def coordinateLinear (B : Adelic.DataTheta.ComparisonData F H K A) (p : IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A) (z : IntrinsicExterior.Intrinsic.Tangent) :
    ((Sum (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A)) → ℂ) →ₗ[ℂ] ((Sum (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A)) → ℂ) :=
  B.complexPhase.symm.toLinearMap.comp ((ambientLinear A p z).comp B.complexPhase.toLinearMap)

theorem coordinateProjector_apply (B : Adelic.DataTheta.ComparisonData F H K A) (p : IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A) (z : IntrinsicExterior.Intrinsic.Tangent)
    (x : Sum (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) → ℂ) :
    (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B p z).mulVec x = B.complexPhase.symm (IntrinsicCompactProjector.IntrinsicParameter.ambientParameter A p z (B.complexPhase x)) := by
  have hM : IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B p z = LinearMap.toMatrix' (coordinateLinear A B p z) := by
    ext i j
    simp [IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector,LinearMap.toMatrix'_apply,coordinateLinear,ambientLinear_apply]
  rw [hM,LinearMap.toMatrix'_mulVec]
  change B.complexPhase.symm (ambientLinear A p z (B.complexPhase x)) = _
  rw [ambientLinear_apply]

theorem coordinateProjector_base_graph (B : Adelic.DataTheta.ComparisonData F H K A) (hG : Adelic.DataTheta.GeometryIdentification B)
    (z : Adelic.BallNatural.Ball) (x : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B (IntrinsicCompactProjector.IntrinsicParameter.baseParameter A) z.val).mulVec
      (Sum.elim x ((B.period z).matrix.mulVec x)) = Sum.elim x ((B.period z).matrix.mulVec x) := by
  let a := (B.frame z).inv.mulVec x
  have ha : (B.frame z).val.mulVec a = x := by
    change (B.frame z).val.mulVec ((B.frame z).inv.mulVec x) = x
    rw [Matrix.mulVec_mulVec,(B.frame z).val_inv,Matrix.one_mulVec]
  have hframe := hG.2.2.2.2.2.2.1 z a
  rw [ha] at hframe
  rw [coordinateProjector_apply,hframe,IntrinsicCompactProjector.IntrinsicParameter.ambientParameter_base_frame,← hframe,
    ContinuousLinearEquiv.symm_apply_apply]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterLinear.Intrinsic
