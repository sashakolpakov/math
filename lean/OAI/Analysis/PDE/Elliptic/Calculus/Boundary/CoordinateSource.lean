import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.UniformSource
import OAI.Analysis.PDE.Schauder.Calculus.Interior.MooreEquation

/-! Simultaneously controlled forcing in all flat coordinate directions,
including the normal direction required by the normal-jet recovery. -/

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Schauder

variable {n m : ℕ}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "X" => EuclideanSpace ℝ (Fin m)
local instance coordinateSourceFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance coordinateSourceFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance coordinateSourceSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance coordinateSourceSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance coordinateSourceEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance coordinateSourceEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance

theorem exists_uniform_coordinate_log_chart_sources
    (e : X ≃ₗᵢ[ℝ] E)
    {Ω K S : Set E} (hΩK : Ω ⊆ K) (hΩ : IsOpen Ω) (hS : IsOpen S)
    (hconv : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (G P : E → E) (hG : ContDiff ℝ 4 G) (hP : ContDiff ℝ 4 P)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    (hinv : ∀ x ∈ S, (fun z => P (G z)) =ᶠ[𝓝 x] id)
    (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 4 B₀)
    {α R N Z : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hR : 0 ≤ R) (hN : 0 ≤ N) (hZ : 0 ≤ Z) :
    ∃ C > 0, ∀ (u f : E → ℝ) (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α),
      ContDiff ℝ 3 u → ‖U‖ ≤ R →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      ∀ (A : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E) α) (W : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] ℝ) α),
      ‖A‖ ≤ N → ‖W‖ ≤ Z →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value W x = (f x)⁻¹ • fderiv ℝ f x) →
      (∀ x ∈ S, DifferentiableAt ℝ f (G x)) →
      (∀ x ∈ S, (fun z => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u z)) =ᶠ[𝓝 (G x)] f) →
      ∃ Q : Fin m → OAI.Analysis.Normed.Function.Holder.HolderMap (e ⁻¹' closure S) ℝ α,
        (∀ i, ‖Q i‖ ≤ C) ∧
        ∀ i x, ∀ hx : e x ∈ S, ellipticTrace
          (fun z => OAI.Analysis.PDE.Dirichlet.isometryConjugate e (pullbackEllipticOperator (fderiv ℝ P (G (e z)))
            (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G (e z))))))
          (OAI.Analysis.PDE.Dirichlet.directionalDerivative (((fun y => u y-B₀ y) ∘ G) ∘ e)
            (EuclideanSpace.single i 1)) x =
            OAI.Analysis.Normed.Function.Holder.HolderMap.value (Q i) ⟨x,subset_closure hx⟩ := by
  have hall (i : Fin m) := exists_uniform_log_chart_source hΩK hΩ hS hconv hcompact hdiam
    G P hG hP hGK hGΩ hinv B₀ hB₀ (e (EuclideanSpace.single i 1))
    (by rw [e.norm_map, PiLp.norm_single]; norm_num) hα hα1 hR hN hZ
  choose c hc hs using hall
  let C := (∑ i, c i)+1
  have hci (i : Fin m) : c i ≤ C := by
    have hsum : c i ≤ ∑ j, c j := Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)
    exact hsum.trans (le_add_of_nonneg_right (by norm_num))
  have hcs : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ => (hc i).le)
  refine ⟨C, by dsimp only [C]; linarith, ?_⟩
  intro u f U hu hUn hU A W hAn hWn hA hW hf heq
  have hq (i : Fin m) := hs i u f U hu hUn hU A W hAn hWn hA hW hf heq
  choose q hqn hqeq using hq
  let g : (e ⁻¹' closure S) → closure S := fun x => ⟨e x,x.property⟩
  have hg : Continuous g := by fun_prop
  have hgLip (x y : e ⁻¹' closure S) : dist (g x) (g y) ≤ (1:ℝ)*dist x y := by
    simpa only [g, Subtype.dist_eq, one_mul] using (e.isometry.dist_eq x y).le
  have hp (i : Fin m) := OAI.Analysis.Normed.Function.Holder.exists_holder_lipschitz_pullback hα (q i) g hg (by norm_num : (0:ℝ) ≤ 1) hgLip
  choose Q hQ hQn using hp
  refine ⟨Q, ?_, ?_⟩
  · intro i
    exact (hQn i).trans (by simpa only [Real.one_rpow, max_self, one_mul] using (hqn i).trans (hci i))
  · intro i x hx
    have hψ : ContDiff ℝ 3 ((fun y => u y-B₀ y) ∘ G) :=
      (hu.sub (hB₀.of_le (by norm_num))).comp (hG.of_le (by norm_num))
    rw [OAI.Analysis.PDE.Schauder.directional_isometry_comp e _ (hψ.differentiable (by norm_num)),
      OAI.Analysis.PDE.Dirichlet.ellipticTrace_isometry_pullback e
        (fun z => pullbackEllipticOperator (fderiv ℝ P (G z))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z)))) _
        (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hψ (by norm_num) _) x,
      hqeq i (e x) hx, hQ]

end OAI.Analysis.PDE.Elliptic
