import OAI.Analysis.PDE.Schauder.Calculus.PacketPushbackCore
import OAI.Analysis.Fourier.WavePackets.MovingPushback

noncomputable section
open Set Module
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Fourier.WavePackets

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {U : Set Z}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "D" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
local instance localFamilyDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance localFamilyDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance localFamilySecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance localFamilySecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- A positive zero of the transformed equation is the genuine Dirichlet
solution on the target fiber. The inverse coordinates are required to be
C² only locally at the closed target fiber; no global extension of the
moving-domain diffeomorphism is assumed. -/
theorem ParameterJetFields.local_family_pushback_identified
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b)
    (hα : 0 ≤ α) (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    {z : Z} (hz : z ∈ U) (w : D)
    (hzero : C.periodicOperator J hrp hα (z,w) = 0)
    (hpos : C.PositiveAt J hα (z,w))
    {Q : OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} (S : OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicSolution Q)
    (Ψ : E → E)
    (hΨ : ∀ y, Q.defining y ≤ 0 → ContDiffAt ℝ 2 Ψ y)
    (hopen : MapsTo Ψ {y | Q.defining y < 0} {x | r x < 0})
    (hclosed : MapsTo Ψ {y | Q.defining y ≤ 0} {x | r x ≤ 0})
    (hboundary : MapsTo Ψ {y | Q.defining y = 0} {x | r x = 0})
    (hperiodic : ∀ l : Submodule.span ℤ (Set.range b), ∀ y,
      Ψ (y + e.symm ((l : P),0)) = Ψ y + e.symm ((l : P),0))
    (hBg : ∀ y (hy : Q.defining y ≤ 0),
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z) ⟨Ψ y,hclosed hy⟩ =
        fderiv ℝ (fderiv ℝ Q.background) y)
    (hJ : ∀ y (hy : Q.defining y ≤ 0),
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian z) ⟨Ψ y,hclosed hy⟩ = fderiv ℝ Ψ y)
    (hK : ∀ y (hy : Q.defining y ≤ 0),
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature z) ⟨Ψ y,hclosed hy⟩ = fderiv ℝ (fderiv ℝ Ψ) y)
    (hF : ∀ y (hy : Q.defining y ≤ 0),
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source z) ⟨Ψ y,hclosed hy⟩ = Q.density y) :
    ∀ y, Q.defining y ≤ 0 →
      physicalPushback Q.background Ψ w y = Q.background y + S.u y := by
  have hfield (y : E) (hy : Q.defining y < 0) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField J hα (z,w)) ⟨Ψ y,hclosed hy.le⟩ =
        OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback Q.background Ψ w) y := by
    exact C.hessianField_eq_local_pushback J hα hr z w Q.background Ψ (Ψ y) y
      (hopen hy) (Q.background_smooth.contDiffAt.of_le (by simp))
      (hΨ y hy.le) rfl (hBg y hy.le) (hJ y hy.le) (hK y hy.le)
  have hpositive (y : E) (hy : Q.defining y < 0) :
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback Q.background Ψ w) y)).PosDef := by
    exact C.local_pushback_positive J hα z w hpos _ _ _ y
      (contDiffAt_physicalPushback_local hr (Q.background_smooth.contDiffAt.of_le (by simp))
        (hΨ y hy.le) (hopen hy) w) (hfield y hy)
  have heq (y : E) (hy : Q.defining y < 0) :
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback Q.background Ψ w) y) =
        Q.density y := by
    exact (C.local_pushback_equation J hα hrp hz w hzero _ _ _ y (hfield y hy)).trans
      (hF y hy.le)
  exact OAI.Analysis.Fourier.WavePackets.movingPushback_identified S hr Ψ
    (fun y hy => (hΨ y hy.le).contDiffWithinAt)
    (fun y hy => (hΨ y hy).continuousAt.continuousWithinAt)
    hopen hclosed hboundary hperiodic w hpositive heq

end OAI.Analysis.PDE.Schauder
