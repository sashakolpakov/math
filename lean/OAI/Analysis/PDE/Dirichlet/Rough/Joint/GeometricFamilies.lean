import OAI.Analysis.PDE.Dirichlet.Rough.Joint.MixedRegularity
import OAI.Analysis.PDE.Dirichlet.Rough.Joint.Interior

noncomputable section
open Set Filter Module Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder

variable {Z T E P V ι : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- The exact combined external/spatial-flow implicit-family output.
Smoothness is required on one open parameter neighborhood, and the
identity is uniform over the closed physical domain. -/
def HasJointGeometricSolutionFamiliesAt
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (r : E → ℝ) (f : Z × E → ℝ)
    (hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}) (α : ℝ) (p₀ : Z) : Prop :=
  ∀ D : ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r,
    ∃ U : Z × T → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ∃ W : Set (Z × T),
      IsOpen W ∧ (p₀,(0:T)) ∈ W ∧ ContDiffOn ℝ ∞ U W ∧
      ∀ᶠ p in 𝓝 (p₀,(0:T)), ∀ x : {x | r x ≤ 0},
        OAI.Analysis.Normed.Function.Holder.C2Holder.value (U p) x = f (p.1,D.map (p.2,x))

variable [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E] [Nontrivial E]
  {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r : E → ℝ} {f : Z × E → ℝ}
  {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ} {p₀ : Z}

omit [FiniteDimensional ℝ Z] in
theorem HasJointGeometricSolutionFamiliesAt.joint_contDiffAt_interior
    (hc : ParameterDeformation.HasJointGeometricSolutionFamiliesAt (T := E) e b r f hΩD α p₀)
    (hr : Continuous r) (hrp : LatticePeriodic e b r)
    {a : E} (ha : r a < 0) : ContDiffAt ℝ ∞ f (p₀,a) := by
  obtain ⟨D,hD⟩ := ParameterDeformation.exists_interior_periodicDomainDeformation e b r hr hrp ha
    (ContinuousLinearMap.id ℝ E)
  obtain ⟨U,W,hW,hp,hU,hvalue⟩ := hc D
  exact ParameterDeformation.joint_contDiffAt_of_interior_flow (hΩD ha)
    ((hU (p₀,0) hp).contDiffAt (hW.mem_nhds hp)) hvalue hD

theorem HasJointGeometricSolutionFamiliesAt.all_joint_mixed_chart_orders
    (hc : ParameterDeformation.HasJointGeometricSolutionFamiliesAt (T := T) e b r f hΩD α p₀)
    (hr : ContDiff ℝ 3 r) (hrp : LatticePeriodic e b r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (j : X ≃ₗᵢ[ℝ] E) (G : X → E) (P' : E → X)
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P')
    (hinv : (fun x ↦ P' (G x)) =ᶠ[𝓝 (0:X)] id)
    (ℓ : X →L[ℝ] ℝ) (c : ℝ)
    (hlevel : ∀ x ∈ ball (0:X) 1, r (G x) = c+ℓ x)
    (A : T →L[ℝ] X) (hA : ∀ t, ℓ (A t) = 0)
    {Q : Set X} (hGQ : MapsTo G Q {x | r x ≤ 0}) :
    ∃ S : Set Z, IsOpen S ∧ p₀ ∈ S ∧
      ∃ O : Set X, IsOpen O ∧ (0:X) ∈ O ∧
        ∀ (N : ℕ) (v : Fin N → Z × T), ContDiffOn ℝ 2
          (fun p : Z × X ↦ iteratedFDeriv ℝ N
            (fun s : Z × T ↦ f (p.1+s.1,G (p.2+A s.2))) 0 v) (S ×ˢ (Q ∩ O)) := by
  obtain ⟨D,hD⟩ := ParameterDeformation.exists_boundary_periodicDomainDeformation j e b r hrp hG hP rfl
    hinv ℓ c hlevel A hA
  obtain ⟨U,W,hW,hp,hU,hvalue⟩ := hc D
  exact ParameterDeformation.all_joint_mixed_tangent_orders hr hreg (hG.of_le (by simp)).contDiffOn hGQ
    hW hU hp A hvalue hD

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
