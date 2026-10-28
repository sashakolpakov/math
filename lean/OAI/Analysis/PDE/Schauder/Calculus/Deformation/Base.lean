import OAI.Analysis.PDE.Schauder.Calculus.PositiveImplicitCurve
import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Zero

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
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
local instance baseDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance baseDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance baseSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance baseSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance baseEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance baseEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance baseMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance baseMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance baseC2Group : NormedAddCommGroup H := inferInstance
local instance baseC2Space : NormedSpace ℝ H := inferInstance
local instance baseC2Module : Module ℝ H := inferInstance
local instance baseC2Bounded : IsBoundedSMul ℝ H := NormedSpace.toIsBoundedSMul
local instance baseC2Continuous : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul
local instance baseC2AddZero : AddZeroClass H := inferInstance

theorem DeformationFields.background_zero_eq
    (C : DeformationFields r α I Φ B₀ f) (h0 : 0 ∈ I)
    (hΦ : ∀ x, Φ (0,x) = x) (B : H)
    (hB : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative B x = fderiv ℝ (fderiv ℝ B₀) x) :
    C.background 0 = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM B := by
  change C.background 0 = B.val.2.2
  exact C.background_zero_eq_field h0 hΦ B.val.2.2 hB

omit [Fintype ι] in
theorem DeformationFields.background_add_second_eq
    (C : DeformationFields r α I Φ B₀ f) (J : LatticeJetLifts hΩK α e b)
    (h0 : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x) (B : H)
    (hB : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative B x = fderiv ℝ (fderiv ℝ B₀) x)
    (v : X) : C.background 0 + J.second v = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM (B+v.val) := by
  have hb : C.background 0 = B.val.2.2 :=
    C.background_zero_eq_field h0 hΦ B.val.2.2 hB
  have hv : J.second v = v.val.val.2.2 :=
    OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective (J.second_value v)
  change C.background 0 + J.second v = B.val.2.2 + v.val.val.2.2
  exact congrArg₂ (· + ·) hb hv

omit [Fintype ι] in
theorem DeformationFields.hessianField_zero
    (C : DeformationFields r α I Φ B₀ f) (J : LatticeJetLifts hΩK α e b)
    (h0 : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x) (hα : 0 ≤ α) (v : X) :
    C.hessianField hα J.first J.second (0,v) =
      OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots) (C.background 0+J.second v) := by
  exact C.hessianField_zero_general h0 hΦ hα J.first J.second v

omit [Fintype ι] in
theorem DeformationFields.hessianField_zero_eq
    (C : DeformationFields r α I Φ B₀ f) (J : LatticeJetLifts hΩK α e b)
    (h0 : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x) (hα : 0 ≤ α) (g : H) (v : X)
    (hbase : C.background 0+J.second v = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    C.hessianField hα J.first J.second (0,v) = OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots g := by
  have hb := congrArg (OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) hbase
  exact (C.hessianField_zero J h0 hΦ hα v).trans hb

theorem PeriodicDeformationFields.periodicOperator_zero_of_equation
    (C : PeriodicDeformationFields r α I Φ B₀ f e b) (J : LatticeJetLifts hΩK α e b)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (h0 : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x)
    (hα : 0 ≤ α) (g : H) (v : X)
    (hbase : C.fields.background 0+J.second v = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g)
    (heq : ∀ x : {x | r x ≤ 0},
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots g) x) = f x) :
    C.periodicOperator J hrp hα (0,v) = 0 := by
  apply Subtype.ext
  have heq' : ∀ x, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value
      (OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots) g.val.2.2) x) = f x := heq
  have hz : C.fields.mooreOperator hα J.first J.second (0,v) = 0 := by
    exact C.fields.mooreOperator_zero_of_field h0 hΦ hα J.first J.second v
      g.val.2.2 hbase heq'
  exact (C.coe_periodicOperator J hrp hα (0,v) h0).trans hz

omit [Fintype ι] in
theorem DeformationFields.positiveAt_zero_of_quadratic
    (C : DeformationFields r α I Φ B₀ f) (J : LatticeJetLifts hΩK α e b)
    (h0 : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x) (hα : 0 ≤ α) (g : H) (v : X)
    (hbase : C.background 0+J.second v = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g)
    (hpos : ∀ x : {x | r x ≤ 0}, ∀ z ∈ sphere (0 : Fin n → Quaternion ℝ) 1,
      0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots g) x) z).re) :
    C.PositiveAt J hα (0,v) := by
  unfold DeformationFields.PositiveAt
  rw [C.hessianField_zero_eq J h0 hΦ hα g v hbase]
  exact hpos

end OAI.Analysis.PDE.Schauder
