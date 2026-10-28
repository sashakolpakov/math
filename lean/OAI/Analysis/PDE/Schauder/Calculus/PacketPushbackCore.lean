import OAI.Analysis.PDE.Schauder.Calculus.Parameter.Value
import OAI.Analysis.PDE.Schauder.Calculus.PositiveImplicitFamily
import OAI.Analysis.PDE.Schauder.Calculus.PhysicalPushback

open Set Module
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {U : Set Z}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "D" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
local instance packetPushDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance packetPushDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance packetPushSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance packetPushSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [Fintype ι] in
/-- Only smoothness at the target point and membership of its inverse image
are needed; the change of variables need not exist globally. -/
theorem contDiffAt_physicalPushback_local (hr : Continuous r)
    {B : E → ℝ} {Ψ : E → E} {y : E}
    (hB : ContDiffAt ℝ 2 B y) (hi : ContDiffAt ℝ 2 Ψ y)
    (hy : r (Ψ y) < 0) (v : D) :
    ContDiffAt ℝ 2 (physicalPushback B Ψ v) y := by
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr continuous_const
  exact hB.add (((OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ v.val).contDiffAt
    (hΩ.mem_nhds hy)).comp y hi)

omit [Fintype ι] in
theorem ParameterJetFields.hessianField_eq_local_pushback
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (hr : Continuous r) (z : Z) (v : D)
    (B : E → ℝ) (Ψ : E → E) (x y : E) (hx : r x < 0)
    (hB : ContDiffAt ℝ 2 B y) (hi : ContDiffAt ℝ 2 Ψ y) (hinv : Ψ y = x)
    (hBg : OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z) ⟨x,hx.le⟩ = fderiv ℝ (fderiv ℝ B) y)
    (hJ : OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian z) ⟨x,hx.le⟩ = fderiv ℝ Ψ y)
    (hK : OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature z) ⟨x,hx.le⟩ = fderiv ℝ (fderiv ℝ Ψ) y) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField J hα (z,v)) ⟨x,hx.le⟩ =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B Ψ v) y := by
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr continuous_const
  apply C.hessianField_value J hα z v B (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v.val))
    Ψ ⟨x,hx.le⟩ y hB
    ((OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ v.val).contDiffAt (hΩ.mem_nhds hx)) hi hinv hBg hJ hK
  · rw [J.first_value]
    exact (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives hΩ v.val hx).1.symm
  · rw [J.second_value]
    exact (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives hΩ v.val hx).2.symm

theorem ParameterJetFields.local_pushback_equation
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) {z : Z} (hz : z ∈ U) (v : D)
    (hzero : C.periodicOperator J hrp hα (z,v) = 0)
    (x : {x | r x ≤ 0}) (B : E → ℝ) (Ψ : E → E) (y : E)
    (hfield : OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField J hα (z,v)) x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B Ψ v) y) :
    OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B Ψ v) y) =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source z) x := by
  have hz' : C.mooreOperator J hα (z,v) = 0 := by
    rw [← C.coe_periodicOperator J hrp hα (z,v) hz,hzero]
    rfl
  have hv := congrArg (fun A => OAI.Analysis.Normed.Function.Holder.HolderMap.value A x) hz'
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedBackgroundMooreField hα (C.background z)
    (C.jacobian z) (C.curvature z) (J.first v) (J.second v)) x -
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source z) x = 0 at hv
  rw [transformedBackgroundMooreField,OAI.Analysis.Normed.Function.Holder.value_mooreDetField] at hv
  change OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField J hα (z,v)) x) - _ = 0 at hv
  rw [hfield] at hv
  exact sub_eq_zero.mp hv

omit [Fintype ι] in
theorem ParameterJetFields.local_pushback_positive
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (z : Z) (v : D) (hpos : C.PositiveAt J hα (z,v))
    (x : {x | r x ≤ 0}) (B : E → ℝ) (Ψ : E → E) (y : E)
    (hc : ContDiffAt ℝ 2 (physicalPushback B Ψ v) y)
    (hfield : OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField J hα (z,v)) x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B Ψ v) y) :
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B Ψ v) y)).PosDef := by
  apply (OAI.Analysis.PDE.Dirichlet.complexify_posDef_iff_unit_sphere _ (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hc)).mpr
  intro q hq
  rw [← hfield]
  exact hpos x q hq

end OAI.Analysis.PDE.Schauder
