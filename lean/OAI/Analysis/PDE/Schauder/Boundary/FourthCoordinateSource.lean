import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.ChartSource
import OAI.Analysis.PDE.Schauder.Calculus.Interior.MooreEquation
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HolderPullback
import OAI.Analysis.Normed.Function.Holder.Boundary.LowerJetHolder

noncomputable section
open Set
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Elliptic OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem double_directional_isometry_comp (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : ContDiff ℝ 2 u) (v w : E) :
    OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ e) v) w =
      (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (e v)) (e w)) ∘ e := by
  rw [directional_isometry_comp e u (hu.differentiable (by norm_num)),
    directional_isometry_comp e (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (e v))
      ((OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 1) (by norm_num) _).differentiable (by norm_num))]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The true twice-coordinate equation and its source norm survive the
orthonormal coordinate change used to single out a normal direction. -/
theorem exists_double_equation_isometry (e : E ≃ₗᵢ[ℝ] F)
    (A : F → F →L[ℝ] F) (u : F → ℝ) (hu : ContDiff ℝ 4 u)
    {S : Set F} {α : ℝ} (hα : 0 ≤ α) (v w : E) (R : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
    (heq : ∀ x : S, OAI.Analysis.PDE.Elliptic.ellipticTrace A
      (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (e v)) (e w)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x) :
    ∃ Q : OAI.Analysis.Normed.Function.Holder.HolderMap (e ⁻¹' S) ℝ α, ‖Q‖ ≤ ‖R‖ ∧
      ∀ x : e ⁻¹' S, OAI.Analysis.PDE.Elliptic.ellipticTrace (fun y => OAI.Analysis.PDE.Dirichlet.isometryConjugate e (A (e y)))
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ e) v) w) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value Q x := by
  let g : (e ⁻¹' S) → S := fun x => ⟨e x,x.property⟩
  have hg : Isometry g := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    simpa only [g,Subtype.dist_eq] using e.isometry.dist_eq (x : E) (y : E)
  refine ⟨holderIsometricPullback hα g hg R, norm_holderIsometricPullback_le hα g hg R, ?_⟩
  intro x
  rw [double_directional_isometry_comp e u (hu.of_le (by norm_num)),
    OAI.Analysis.PDE.Dirichlet.ellipticTrace_isometry_pullback e A _
      (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative
        (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 3) (by norm_num) _) (m := 2) (by norm_num) _)]
  exact heq (g x)

local instance fourthCoordinateE1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthCoordinateE1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthCoordinateE2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthCoordinateE2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthCoordinateF1Group : NormedAddCommGroup (F →L[ℝ] ℝ) := inferInstance
local instance fourthCoordinateF1Space : NormedSpace ℝ (F →L[ℝ] ℝ) := inferInstance
local instance fourthCoordinateF2Group : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
local instance fourthCoordinateF2Space : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The Hessian of a twice-tangential field has the same Hölder bound in
orthonormal coordinates; C² regularity of that field suffices. -/
theorem exists_second_holder_isometry (e : E ≃ₗᵢ[ℝ] F)
    (q : F → ℝ) (hq : ContDiff ℝ 2 q) {S : Set F} {α : ℝ} (hα : 0 ≤ α)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap S (F →L[ℝ] F →L[ℝ] ℝ) α)
    (hB : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = fderiv ℝ (fderiv ℝ q) x) :
    ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap (e ⁻¹' S) (E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : e ⁻¹' S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ (q ∘ e)) x) ∧ ‖H‖ ≤ ‖B‖ := by
  have hq' : ContDiff ℝ 1 (fderiv ℝ (q ∘ e)) :=
    (hq.comp e.contDiff).fderiv_right (by norm_num)
  apply OAI.Analysis.Normed.Function.Holder.exists_holder_field_of_bounds hα (norm_nonneg B) _
    (hq'.continuous_fderiv one_ne_zero).continuousOn
  · intro x hx
    rw [OAI.Analysis.PDE.Dirichlet.norm_second_isometry_comp e q hq, ← hB ⟨e x,hx⟩]
    exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le B _
  · intro x hx y hy
    rw [OAI.Analysis.PDE.Dirichlet.norm_second_sub_isometry_comp e q hq, ← hB ⟨e x,hx⟩, ← hB ⟨e y,hy⟩]
    simpa only [Subtype.dist_eq,e.isometry.dist_eq,dist_eq_norm] using
      OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le B ⟨e x,hx⟩ ⟨e y,hy⟩

end OAI.Analysis.PDE.Schauder
