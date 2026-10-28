import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.Fields
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.Value
import OAI.Analysis.PDE.Schauder.Calculus.PositiveImplicitFamily
import OAI.Analysis.PDE.Schauder.Calculus.DomainPushback

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : CoordinateSpace n 4 → ℝ} {α : ℝ} {U : Set Z}
  {Φ : Z × CoordinateSpace n 4 → CoordinateSpace n 4}
  {B₀ f : CoordinateSpace n 4 → ℝ}
  {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => CoordinateSpace n 4
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
theorem inverseFamily_preserves_domain {t : Z}
    (hb : Function.Bijective (fun x ↦ Φ (t,x)))
    (hdom : ∀ x, r (Φ (t,x)) < 0 ↔ r x < 0) (y : E) :
    r (ParameterDeformation.inverseFamily Φ t y) < 0 ↔ r y < 0 := by
  simpa only [ParameterDeformation.inverseFamily, Function.invFun_eq (hb.surjective y)] using
    (hdom (ParameterDeformation.inverseFamily Φ t y)).symm

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
theorem inverseFamily_preserves_closed_domain {t : Z}
    (hb : Function.Bijective (fun x ↦ Φ (t,x)))
    (hdom : ∀ x, r (Φ (t,x)) ≤ 0 ↔ r x ≤ 0) (y : E) :
    r (ParameterDeformation.inverseFamily Φ t y) ≤ 0 ↔ r y ≤ 0 := by
  simpa only [ParameterDeformation.inverseFamily, Function.invFun_eq (hb.surjective y)] using
    (hdom (ParameterDeformation.inverseFamily Φ t y)).symm

theorem contDiff_inverseFamily_slice
    (hi : ContDiffOn ℝ ∞ (fun p : Z × E ↦ ParameterDeformation.inverseFamily Φ p.1 p.2) {p | p.1 ∈ U})
    {t : Z} (ht : t ∈ U) : ContDiff ℝ ∞ (ParameterDeformation.inverseFamily Φ t) := by
  apply contDiffOn_univ.mp
  exact hi.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ ↦ ht)

local instance parameterPushDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance parameterPushDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance parameterPushSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterPushSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [Fintype ι] in
/-- Exact physical Hessian of the positive implicit family, with the
geometric coefficient identities stated explicitly. -/
theorem parameter_hessianField_eq_pushback
    (C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α U e b) (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (hr : Continuous r) (hB : ContDiff ℝ 2 B₀)
    {t : Z} (hbij : Function.Bijective (fun x ↦ Φ (t,x)))
    (hi : ContDiff ℝ 2 (ParameterDeformation.inverseFamily Φ t))
    (hJ : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian t) x = ParameterDeformation.inverseJacobian Φ (t,x))
    (hT : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature t) x = ParameterDeformation.inverseHessian Φ (t,x))
    (hBg : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background t) x = fderiv ℝ (fderiv ℝ B₀) (Φ (t,x)))
    (v : X) {x : E} (hx : r x < 0) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField J hα (t,v)) ⟨x,hx.le⟩ =
      quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.PDE.Schauder.physicalPushback B₀ (ParameterDeformation.inverseFamily Φ t) v) (Φ (t,x)) := by
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr continuous_const
  apply C.hessianField_value J hα t v B₀
    (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v.val)) (ParameterDeformation.inverseFamily Φ t) ⟨x,hx.le⟩ (Φ (t,x))
    hB.contDiffAt ((OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ v.val).contDiffAt (hΩ.mem_nhds hx))
    hi.contDiffAt (Function.leftInverse_invFun hbij.injective x) (hBg _)
    (hJ _) (hT _)
  · rw [J.first_value]
    exact (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives hΩ v.val hx).1.symm
  · rw [J.second_value]
    exact (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives hΩ v.val hx).2.symm

theorem parameter_pushback_equation
    (C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α U e b) (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (hr : Continuous r) (hrp : LatticePeriodic e b r) (hB : ContDiff ℝ 2 B₀)
    {t : Z} (ht : t ∈ U) (hbij : Function.Bijective (fun x ↦ Φ (t,x)))
    (hi : ContDiff ℝ 2 (ParameterDeformation.inverseFamily Φ t))
    (hdom : ∀ x, r (Φ (t,x)) < 0 ↔ r x < 0)
    (hJ : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian t) x = ParameterDeformation.inverseJacobian Φ (t,x))
    (hT : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature t) x = ParameterDeformation.inverseHessian Φ (t,x))
    (hBg : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background t) x = fderiv ℝ (fderiv ℝ B₀) (Φ (t,x)))
    (hF : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source t) x = f (Φ (t,x)))
    (v : X) (hzero : C.periodicOperator J hrp hα (t,v) = 0) :
    ∀ y, r y < 0 → OAI.LinearAlgebra.Moore.mooreDet n
      (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.PDE.Schauder.physicalPushback B₀ (ParameterDeformation.inverseFamily Φ t) v) y) = f y := by
  intro y hy
  let x := ParameterDeformation.inverseFamily Φ t y
  have hx : r x < 0 := (ParameterDeformation.inverseFamily_preserves_domain hbij hdom y).mpr hy
  have hxy : Φ (t,x) = y := Function.invFun_eq (hbij.surjective y)
  have hfield := ParameterDeformation.parameter_hessianField_eq_pushback C J hα hr hB hbij hi hJ hT hBg v hx
  have hz : C.mooreOperator J hα (t,v) = 0 := by
    rw [← C.coe_periodicOperator J hrp hα (t,v) ht,hzero]
    rfl
  have hv := congrArg (fun A ↦ OAI.Analysis.Normed.Function.Holder.HolderMap.value A (⟨x,hx.le⟩ : {x | r x ≤ 0})) hz
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Schauder.transformedBackgroundMooreField hα (C.background t)
    (C.jacobian t) (C.curvature t) (J.first v) (J.second v)) ⟨x,hx.le⟩ -
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source t) ⟨x,hx.le⟩ = 0 at hv
  rw [OAI.Analysis.PDE.Schauder.transformedBackgroundMooreField,OAI.Analysis.Normed.Function.Holder.value_mooreDetField] at hv
  change OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField J hα (t,v))
    ⟨x,hx.le⟩) - OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source t) ⟨x,hx.le⟩ = 0 at hv
  rw [hfield,hF,hxy] at hv
  exact sub_eq_zero.mp hv

omit [Fintype ι] in
theorem parameter_pushback_positive
    (C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α U e b) (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (hr : Continuous r) (hB : ContDiff ℝ 2 B₀)
    {t : Z} (hbij : Function.Bijective (fun x ↦ Φ (t,x)))
    (hi : ContDiff ℝ 2 (ParameterDeformation.inverseFamily Φ t))
    (hdom : ∀ x, r (Φ (t,x)) < 0 ↔ r x < 0)
    (hJ : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian t) x = ParameterDeformation.inverseJacobian Φ (t,x))
    (hT : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature t) x = ParameterDeformation.inverseHessian Φ (t,x))
    (hBg : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background t) x = fderiv ℝ (fderiv ℝ B₀) (Φ (t,x)))
    (v : X) (hpos : C.PositiveAt J hα (t,v)) :
    ∀ y, r y < 0 → (OAI.LinearAlgebra.Moore.complexify
      (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.PDE.Schauder.physicalPushback B₀ (ParameterDeformation.inverseFamily Φ t) v) y)).PosDef := by
  intro y hy
  let x := ParameterDeformation.inverseFamily Φ t y
  have hx : r x < 0 := (ParameterDeformation.inverseFamily_preserves_domain hbij hdom y).mpr hy
  have hxy : Φ (t,x) = y := Function.invFun_eq (hbij.surjective y)
  have hc := OAI.Analysis.PDE.Schauder.contDiffOn_physicalPushback_of_mapsTo hr hB hi
    (fun y hy ↦ (ParameterDeformation.inverseFamily_preserves_domain hbij hdom y).mpr hy) v
  have hherm := quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots
    (hc.contDiffAt ((isOpen_lt hr continuous_const).mem_nhds hy))
  apply (complexify_posDef_iff_unit_sphere _ hherm).mpr
  intro z hz
  have hh := ParameterDeformation.parameter_hessianField_eq_pushback C J hα hr hB hbij hi hJ hT hBg v hx
  rw [hxy] at hh
  rw [← hh]
  exact hpos ⟨x,hx.le⟩ z hz

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
