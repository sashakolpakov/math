import OAI.Analysis.PDE.Dirichlet.C2HolderQuaternion
import OAI.Analysis.Normed.Function.Holder.C2HolderCompactLimit
import OAI.Analysis.PDE.Dirichlet.EquationLimit

open Set Filter
open scoped Topology BoundedContinuousFunction Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

theorem value_tendsto {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}
    {f : ℕ → C2Holder (F := F) hΩK α} {g : C2Holder (F := F) hΩK α}
    (h : Tendsto f atTop (𝓝 g)) (x : K) :
    Tendsto (fun k ↦ C2Holder.value (f k) x) atTop (𝓝 (C2Holder.value g x)) :=
  ((BoundedContinuousFunction.evalCLM ℝ x).continuous.comp C2Holder.valueCLM.continuous).tendsto g |>.comp h

end OAI.Analysis.Normed.Function.Holder.C2Holder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

theorem quaternionHessianField_tendsto {n s : ℕ} {Ω K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    {hΩK : Ω ⊆ K} {α : ℝ} (slots : Fin s → OAI.Analysis.PDE.Dirichlet.Q)
    {f : ℕ → C2Holder (F := ℝ) hΩK α} {g : C2Holder (F := ℝ) hΩK α}
    (h : Tendsto f atTop (𝓝 g)) (x : K) :
    Tendsto (fun k ↦ OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α slots (f k)) x)
      atTop (𝓝 (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α slots g) x)) := by
  have hc : Continuous (fun u : C2Holder (F := ℝ) hΩK α ↦
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α slots u) x) :=
    (BoundedContinuousFunction.evalCLM ℝ x).continuous.comp
      (OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM.continuous.comp (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α slots).continuous)
  exact (hc.tendsto g).comp h

/-- The equation and strict positivity survive a Banach-space limit,
including at boundary points of the closed domain. -/
theorem mooreField_equation_posDef_limit {n : ℕ} {Ω K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)}
    {hΩK : Ω ⊆ K} {α : ℝ}
    {f : ℕ → C2Holder (F := ℝ) hΩK α} {g : C2Holder (F := ℝ) hΩK α}
    (h : Tendsto f atTop (𝓝 g)) (x : K) {F : ℕ → ℝ} {b : ℝ}
    (hF : Tendsto F atTop (𝓝 b)) (hb : 0 < b)
    (heq : ∀ k, OAI.LinearAlgebra.Moore.mooreDet n
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (f k)) x) = F k)
    (hpos : ∀ k, (OAI.LinearAlgebra.Moore.complexify
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (f k)) x)).PosDef) :
    OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots g) x) = b ∧
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots g) x)).PosDef := by
  have hA := OAI.Analysis.PDE.Dirichlet.quaternionHessianField_tendsto OAI.Analysis.Calculus.Quaternion.fourSlots h x
  have hd := (OAI.LinearAlgebra.Moore.continuous_mooreDet n).continuousAt.tendsto.comp hA
  have he : OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots g) x) = b := by
    apply tendsto_nhds_unique hd
    change Tendsto (fun k ↦ OAI.LinearAlgebra.Moore.mooreDet n
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (f k)) x)) atTop (𝓝 b)
    simpa only [heq] using hF
  have hsem := OAI.Analysis.PDE.Dirichlet.complexify_posSemidef_of_tendsto hA (fun k ↦ (hpos k).posSemidef)
  exact ⟨he, OAI.Analysis.PDE.Dirichlet.complexify_posDef_of_posSemidef_mooreDet_pos _ hsem (by rwa [he])⟩

theorem quaternionHessianField_eq_of_secondDerivative_eq {n s : ℕ}
    {Ω K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} {hΩK : Ω ⊆ K} {α : ℝ} (slots : Fin s → OAI.Analysis.PDE.Dirichlet.Q)
    (g : C2Holder (F := ℝ) hΩK α) (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (x : K)
    (h : OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x = fderiv ℝ (fderiv ℝ f) x) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α slots g) x = OAI.Analysis.PDE.Dirichlet.quaternionHessian slots f x := by
  change OAI.Analysis.Calculus.Quaternion.hessianMap slots (fun i j ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x
    (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)) = _
  rw [h]
  rfl

end OAI.Analysis.PDE.Dirichlet
