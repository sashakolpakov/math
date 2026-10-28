import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Hessian
import OAI.Analysis.PDE.Schauder.Calculus.Periodic.DeformationOperator
import OAI.Analysis.PDE.Schauder.Calculus.PhysicalPushback
import OAI.Analysis.PDE.Dirichlet.PositiveOpen

open Set Metric Module
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {I : Set ℝ}
  {Φ : ℝ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
  {B₀ f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

omit [Fintype ι] in
theorem DeformationFields.hessianField_eq_pushback
    (C : DeformationFields r α I Φ B₀ f) (J : LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (hr : Continuous r) (hB : ContDiff ℝ 2 B₀)
    {t : ℝ} (ht : t ∈ I) (hbij : Function.Bijective (fun x => Φ (t,x)))
    (hi : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t)) (v : X)
    {x : E} (hx : r x < 0) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField hα J.first J.second (t,v)) ⟨x,hx.le⟩ =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B₀ (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t) v) (Φ (t,x)) := by
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr continuous_const
  apply C.hessianField_value hα J.first J.second ht v
    (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v.val)) ⟨x,hx.le⟩ hbij hB.contDiffAt
    ((OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ v.val).contDiffAt (hΩ.mem_nhds hx)) hi.contDiffAt
  · rw [J.first_value]
    exact (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives hΩ v.val hx).1.symm
  · rw [J.second_value]
    exact (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives hΩ v.val hx).2.symm

theorem PeriodicDeformationFields.pushback_equation
    (C : PeriodicDeformationFields r α I Φ B₀ f e b) (J : LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hB : ContDiff ℝ 2 B₀)
    {t : ℝ} (ht : t ∈ I) (hbij : Function.Bijective (fun x => Φ (t,x)))
    (hi : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t)) (hlevel : ∀ x, r (Φ (t,x)) = r x)
    (v : X) (hzero : C.periodicOperator J hrp hα (t,v) = 0) :
    ∀ y, r y < 0 → OAI.LinearAlgebra.Moore.mooreDet n
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B₀ (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t) v) y) = f y := by
  intro y hy
  let x := OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t y
  have hx : r x < 0 := by
    simpa only [x,OAI.Analysis.PDE.Dirichlet.inverseFamily_preserves_level t hbij r hlevel y] using hy
  have hxy : Φ (t,x) = y := Function.invFun_eq (hbij.surjective y)
  have hfield := C.fields.hessianField_eq_pushback J hα hr hB ht hbij hi v hx
  have hz : C.fields.mooreOperator hα J.first J.second (t,v) = 0 := by
    rw [← C.coe_periodicOperator J hrp hα (t,v) ht,hzero]
    rfl
  have hv := congrArg (fun A => OAI.Analysis.Normed.Function.Holder.HolderMap.value A (⟨x,hx.le⟩ : {x | r x ≤ 0})) hz
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedBackgroundMooreField hα (C.fields.background t)
    (C.fields.jacobian t) (C.fields.curvature t) (J.first v) (J.second v)) ⟨x,hx.le⟩ -
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.fields.source t) ⟨x,hx.le⟩ = 0 at hv
  rw [transformedBackgroundMooreField,OAI.Analysis.Normed.Function.Holder.value_mooreDetField] at hv
  change OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.fields.hessianField hα J.first J.second (t,v))
    ⟨x,hx.le⟩) - OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.fields.source t) ⟨x,hx.le⟩ = 0 at hv
  rw [hfield,C.fields.source_value t ht,hxy] at hv
  exact sub_eq_zero.mp hv

omit [Fintype ι] in
theorem DeformationFields.pushback_positive
    (C : DeformationFields r α I Φ B₀ f) (J : LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (hr : Continuous r) (hB : ContDiff ℝ 2 B₀)
    {t : ℝ} (ht : t ∈ I) (hbij : Function.Bijective (fun x => Φ (t,x)))
    (hi : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t)) (hlevel : ∀ x, r (Φ (t,x)) = r x)
    (v : X) (hpos : ∀ x : {x | r x ≤ 0}, ∀ z ∈ sphere (0 : Fin n → Quaternion ℝ) 1,
      0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField hα J.first J.second (t,v)) x) z).re) :
    ∀ y, r y < 0 → (OAI.LinearAlgebra.Moore.complexify
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B₀ (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t) v) y)).PosDef := by
  intro y hy
  let x := OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t y
  have hx : r x < 0 := by
    simpa only [x,OAI.Analysis.PDE.Dirichlet.inverseFamily_preserves_level t hbij r hlevel y] using hy
  have hxy : Φ (t,x) = y := Function.invFun_eq (hbij.surjective y)
  have hc := contDiffOn_physicalPushback hr hB hi (OAI.Analysis.PDE.Dirichlet.inverseFamily_preserves_level t hbij r hlevel) v
  have hherm := OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots
    (hc.contDiffAt ((isOpen_lt hr continuous_const).mem_nhds hy))
  apply (OAI.Analysis.PDE.Dirichlet.complexify_posDef_iff_unit_sphere _ hherm).mpr
  intro z hz
  have hh := C.hessianField_eq_pushback J hα hr hB ht hbij hi v hx
  rw [hxy] at hh
  rw [← hh]
  exact hpos ⟨x,hx.le⟩ z hz

end OAI.Analysis.PDE.Schauder
