import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Hessian
import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Periodic
import OAI.Analysis.PDE.Schauder.Calculus.LatticeJets

open Set Module
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {I : Set ℝ}
  {Φ : ℝ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
  {B₀ f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}

omit [Fintype ι] in
theorem PeriodicDeformationFields.hessianField_periodic
    (C : PeriodicDeformationFields r α I Φ B₀ f e b) (J : LatticeJetLifts hΩK α e b)
    (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α) {t : ℝ} (ht : t ∈ I)
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.fields.hessianField hα J.first J.second (t,v)))) := by
  apply holder_periodic_of_value_eq e b hr
  intro x y l hy
  have hBg := holder_value_eq_of_periodic e b (C.fields.background t)
    (C.background_periodic t ht) x y l hy
  have hJ := holder_value_eq_of_periodic e b (C.fields.jacobian t)
    (C.jacobian_periodic t ht) x y l hy
  have hT := holder_value_eq_of_periodic e b (C.fields.curvature t)
    (C.curvature_periodic t ht) x y l hy
  have hp := holder_value_eq_of_periodic e b (J.first v) (J.first_periodic v) x y l hy
  have hB := holder_value_eq_of_periodic e b (J.second v) (J.second_periodic v) x y l hy
  change OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j =>
    (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.fields.background t) y +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedHessianField hα (C.fields.jacobian t)
        (C.fields.curvature t) (J.first v) (J.second v)) y) (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)) =
    OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j =>
    (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.fields.background t) x +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedHessianField hα (C.fields.jacobian t)
        (C.fields.curvature t) (J.first v) (J.second v)) x) (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j))
  congr 1
  funext i j
  simp only [add_apply,value_transformedHessianField,hBg,hJ,hT,hp,hB]

end OAI.Analysis.PDE.Schauder
