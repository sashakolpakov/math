import OAI.Analysis.PDE.Schauder.Calculus.PushbackEquation
import OAI.Analysis.PDE.Schauder.Calculus.PushbackComparison

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

theorem inverseFamily_preserves_domain {t : ℝ}
    (hb : Function.Bijective (fun x => Φ (t,x)))
    (hdom : ∀ x, r (Φ (t,x)) < 0 ↔ r x < 0) (y : E) :
    r (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t y) < 0 ↔ r y < 0 := by
  simpa only [OAI.Analysis.PDE.Dirichlet.inverseFamily, Function.invFun_eq (hb.surjective y)] using
    (hdom (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t y)).symm

theorem inverseFamily_preserves_closed_domain {t : ℝ}
    (hb : Function.Bijective (fun x => Φ (t,x)))
    (hdom : ∀ x, r (Φ (t,x)) ≤ 0 ↔ r x ≤ 0) (y : E) :
    r (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t y) ≤ 0 ↔ r y ≤ 0 := by
  simpa only [OAI.Analysis.PDE.Dirichlet.inverseFamily, Function.invFun_eq (hb.surjective y)] using
    (hdom (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t y)).symm

theorem PeriodicDeformationFields.pushback_equation_of_domain
    (C : PeriodicDeformationFields r α I Φ B₀ f e b) (J : LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hB : ContDiff ℝ 2 B₀)
    {t : ℝ} (ht : t ∈ I) (hbij : Function.Bijective (fun x => Φ (t,x)))
    (hi : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t))
    (hdom : ∀ x, r (Φ (t,x)) < 0 ↔ r x < 0)
    (v : X) (hzero : C.periodicOperator J hrp hα (t,v) = 0) :
    ∀ y, r y < 0 → OAI.LinearAlgebra.Moore.mooreDet n
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B₀ (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t) v) y) = f y := by
  intro y hy
  let x := OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t y
  have hx : r x < 0 := (inverseFamily_preserves_domain hbij hdom y).mpr hy
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
theorem DeformationFields.pushback_positive_of_domain
    (C : DeformationFields r α I Φ B₀ f) (J : LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (hr : Continuous r) (hB : ContDiff ℝ 2 B₀)
    {t : ℝ} (ht : t ∈ I) (hbij : Function.Bijective (fun x => Φ (t,x)))
    (hi : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t))
    (hdom : ∀ x, r (Φ (t,x)) < 0 ↔ r x < 0)
    (v : X) (hpos : ∀ x : {x | r x ≤ 0}, ∀ z ∈ sphere (0 : Fin n → Quaternion ℝ) 1,
      0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField hα J.first J.second (t,v)) x) z).re) :
    ∀ y, r y < 0 → (OAI.LinearAlgebra.Moore.complexify
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B₀ (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t) v) y)).PosDef := by
  intro y hy
  let x := OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t y
  have hx : r x < 0 := (inverseFamily_preserves_domain hbij hdom y).mpr hy
  have hxy : Φ (t,x) = y := Function.invFun_eq (hbij.surjective y)
  have hc := contDiffOn_physicalPushback_of_mapsTo hr hB hi
    (fun y hy => (inverseFamily_preserves_domain hbij hdom y).mpr hy) v
  have hherm := OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots
    (hc.contDiffAt ((isOpen_lt hr continuous_const).mem_nhds hy))
  apply (OAI.Analysis.PDE.Dirichlet.complexify_posDef_iff_unit_sphere _ hherm).mpr
  intro z hz
  have hh := C.hessianField_eq_pushback J hα hr hB ht hbij hi v hx
  rw [hxy] at hh
  rw [← hh]
  exact hpos ⟨x,hx.le⟩ z hz

theorem physicalPushback_identified_of_domain
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {ψ : E → ℝ}
    (hr : ContDiff ℝ 2 r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hB : ContDiff ℝ 2 B₀) (hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b B₀)
    (hψ : ContDiffOn ℝ 2 ψ {x | r x < 0}) (hψc : ContinuousOn ψ {x | r x ≤ 0})
    (hψp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b ψ)
    (hψpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hψbd : ∀ x, r x = 0 → ψ x = B₀ x)
    {F Ψ : E → E} (hΨ : ContDiff ℝ 2 Ψ) (hleft : Function.LeftInverse Ψ F)
    (hFclosed : MapsTo F {x | r x ≤ 0} {x | r x ≤ 0})
    (hΨdom : MapsTo Ψ {x | r x < 0} {x | r x < 0})
    (hΨclosed : MapsTo Ψ {x | r x ≤ 0} {x | r x ≤ 0})
    (hΨbd : MapsTo Ψ {x | r x = 0} {x | r x = 0})
    (hΨp : ∀ l : Submodule.span ℤ (Set.range b), ∀ x,
      Ψ (x+e.symm ((l:P),0)) = Ψ x+e.symm ((l:P),0))
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)
    (hvpos : ∀ x, r x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B₀ Ψ v) x)).PosDef)
    (hvdet : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B₀ Ψ v) x) =
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)) :
    ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value v.val x = ψ (F x)-B₀ (F x) := by
  have heq := OAI.Analysis.PDE.Dirichlet.quaternionic_dirichlet_uniqueness_continuous_lattice hn e b hK
    (contDiffOn_physicalPushback_of_mapsTo hr.continuous hB hΨ hΨdom v) hψ hr
    (continuousOn_physicalPushback_of_mapsTo hB.continuous hΨ.continuous hΨclosed v) hψc hbounded
    hrp (latticePeriodic_physicalPushback hBp hΨp v) hψp hrpos hvpos hψpos hvdet
    (fun x hx => (physicalPushback_boundary_of_mapsTo hΨbd v hx).trans (hψbd x hx).symm)
  intro x
  rw [← physicalPushback_pullback hleft v x,heq (F x) (hFclosed x.property)]

end OAI.Analysis.PDE.Schauder
