import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.Base
import OAI.Analysis.PDE.Dirichlet.Rough.Moore.DerivativeShift
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.Inverse
import OAI.Analysis.Fourier.WavePackets.ParameterBaseAlgebra
import OAI.Analysis.Normed.Function.Holder.C2HolderEquationLimit

noncomputable section
open Set Filter Module Metric
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : CoordinateSpace n 4 → ℝ} {α : ℝ}
  {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => CoordinateSpace n 4
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

local instance parameterIFTDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance parameterIFTDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance parameterIFTSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterIFTSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterIFTC2Group : NormedAddCommGroup H := inferInstance
local instance parameterIFTC2Space : NormedSpace ℝ H := inferInstance
local instance parameterIFTC2Module : Module ℝ H := inferInstance
local instance parameterIFTC2Bounded : IsBoundedSMul ℝ H := NormedSpace.toIsBoundedSMul
local instance parameterIFTC2Continuous : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul
local instance parameterIFTC2AddZero : AddZeroClass H := inferInstance

/-- Genuine smooth solution families in every Banach parameter space,
derived from the actual invertible Moore derivative. -/
theorem hasGeometricSolutionFamilies_of_invertible
    (hn : 1 ≤ n) {K : Set V} (hK : IsCompact K)
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (B₀ f : E → ℝ) (hB₀ : ContDiff ℝ ∞ B₀) (hf : ContDiff ℝ ∞ f)
    (hB₀p : LatticePeriodic e b B₀) (hfp : LatticePeriodic e b f)
    (B : H) (hBp : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value B)))
    (hB₂ : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative B x = fderiv ℝ (fderiv ℝ B₀) x)
    (u : X) (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψp : LatticePeriodic e b ψ)
    (hψbd : ∀ x, r x = 0 → ψ x = B₀ x)
    (hψ₂ : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (B+u.val) x =
      fderiv ℝ (fderiv ℝ ψ) x)
    (hpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = f x)
    (hΩ : IsOpen {x | r x < 0}) (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (hinv : (fderiv ℝ (periodicMooreDirichletOperator hΩ hclosure
      (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots B hBp) u).IsInvertible) :
    ParameterDeformation.HasGeometricSolutionFamilies (Z := Z) e b r ψ B₀ hΩK α := by
  obtain ⟨J⟩ := OAI.Analysis.PDE.Schauder.nonempty_latticeJetLifts (by omega) e b hK hr hrp hbounded hreg hΩK hα hα1
  have hgp : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value (B+u.val))) := by
    change LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value B+OAI.Analysis.Normed.Function.Holder.C2Holder.value u.val))
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_add]
    exact hBp.add u.property.2
  have hH (x : {x | r x ≤ 0}) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val)) x =
        quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x :=
    quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val) ψ x (hψ₂ x)
  intro D
  obtain ⟨C,hCJ,hCT,hCB,hCF⟩ := D.exists_parameter_fields hK hr.continuous hrp hbounded
    hα.le hα1 B₀ f hB₀ hf hB₀p.fderiv.fderiv hfp
  have hI : IsOpen {t : Z | ‖t‖ < D.radius} := isOpen_lt continuous_norm continuous_const
  have h0 : (0 : Z) ∈ {t | ‖t‖ < D.radius} := by simpa using D.radius_pos
  have hj := ParameterDeformation.parameter_jacobian_zero C D.at_zero (hCJ 0 h0)
  have hk := ParameterDeformation.parameter_curvature_zero C D.at_zero (hCT 0 h0)
  have hbase := ParameterDeformation.parameter_background_add_second_eq C J D.at_zero B hB₂ (hCB 0 h0) u
  have hh := OAI.Analysis.Fourier.WavePackets.parameter_hessianField_base C J hα.le 0 u (B+u.val) hj hk hbase
  have hzero : C.periodicOperator J hrp hα.le (0,u) = 0 := by
    apply OAI.Analysis.Fourier.WavePackets.parameter_periodicOperator_zero C J hrp hα.le h0 u
    intro x
    rw [hh,hH x,hCF 0 h0,D.at_zero]
    exact heq x x.property
  have hshift := fderiv_periodicMooreDirichletOperator_shift hΩ hclosure
    (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots
    B (B+u.val) hBp hgp u rfl
  have hder := C.partial_fderiv_base_isInvertible J hrp hα.le hI 0 h0 hj hk hΩ hclosure
    (hrp.comp (fun t ↦ t < 0)) (hrp.comp (fun t ↦ t ≤ 0)) (B+u.val) hgp u hbase
    (by rw [hshift]; exact hinv)
  have hpositive : C.PositiveAt J hα.le (0,u) := by
    intro x z hz
    rw [hh,hH x]
    exact (complexify_posDef_iff_unit_sphere _
      (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hψ.contDiffAt)).mp (hpos x x.property) z hz
  obtain ⟨v,hv,hv0,hvalue⟩ := ParameterDeformation.exists_smooth_geometric_solution_family hn C J hK
    (hr.of_le (by simp)) hrp hbounded hrpos (hB₀.of_le (by simp)) hB₀p
    ψ hψ.contDiffOn hψ.continuous.continuousOn hψp (fun x hx ↦ hpos x hx.le) hψbd
    (fun x hx ↦ heq x hx.le) D.bijective D.inverse_smooth
    (fun t ht l x ↦ D.equivariant t l x) D.open_domain D.closed_domain
    hCJ hCT hCB hCF hα.le hI h0 u hzero hder hpositive
  let inc : X →L[ℝ] H := (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL
  refine ⟨fun t ↦ inc (v t),?_,hvalue⟩
  exact inc.contDiff.contDiffAt.comp 0 hv

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
