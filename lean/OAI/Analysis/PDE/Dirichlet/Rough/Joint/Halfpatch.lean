import OAI.Analysis.PDE.Dirichlet.Rough.Joint.BoundarySmooth
import OAI.Analysis.PDE.Dirichlet.Rough.Joint.SmoothExtension

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

attribute [local instance] linearizedFirstGroup linearizedFirstSpace
  linearizedSecondGroup linearizedSecondSpace

variable {m : ℕ} {Z E : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "W" => EuclideanSpace ℝ (Fin m)

/-- Joint regularity and genuine smooth extension from the mixed
implicit-family derivatives and the actual spatial normal equation. -/
theorem exists_smooth_joint_halfpatch_representative
    (e : W ≃L[ℝ] Z × E) (k : E →L[ℝ] ℝ)
    (F : Z × NonlinearJet E → ℝ) (hF : ContDiff ℝ ∞ F)
    (ν : W) (hν : (k.comp (reindexSpatialProjection e)) ν = 1)
    {O : Set W} (hO : IsOpen O) {S : Set (Z × E)}
    {f : Z × E → ℝ} {g : W → ℝ} (hg : ContDiff ℝ 2 g)
    (hext : EqOn g (f ∘ e) ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O))
    (hmaps : MapsTo e ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O) S)
    (hi : ∀ x ∈ O, 0 < (k.comp (reindexSpatialProjection e)) x → ContDiffAt ℝ ∞ g x)
    (hmixed : ∀ (N : ℕ) (v : Fin N → Z × k.ker),
      ContDiffOn ℝ 2 (fun p : Z × E ↦ iteratedFDeriv ℝ N
        (fun t : Z × k.ker ↦ f (p.1+t.1,p.2+(t.2:E))) 0 v) S)
    (he : ∀ x ∈ ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O),
      F (parameterJetProjection (reindexParameterProjection e) (reindexSpatialProjection e)
        (reindexSpatialInclusion e) (nonlinearTwoJet g x)) = 0)
    (hell : ∀ x ∈ ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O),
      fderiv ℝ (fun a ↦ F ((e x).1,a))
        (parameterJetProjection (reindexParameterProjection e) (reindexSpatialProjection e)
          (reindexSpatialInclusion e) (nonlinearTwoJet g x)).2
        (0,k.smulRight k) ≠ 0)
    {x₀ : W} (hx₀ : x₀ ∈ O) (hxk : (k.comp (reindexSpatialProjection e)) x₀ = 0) :
    ∃ V : Set W, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ O ∧
      ∃ u : W → ℝ, ContDiff ℝ ∞ u ∧
        EqOn u (f ∘ e) ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ V) := by
  have hginfty := contDiffOn_infty_joint_extension e k F hF ν hν hO hg hext hmaps hi hmixed he hell
  obtain ⟨V,hV,hxV,hVO,u,hu,hug⟩ := exists_smooth_extension_halfpatch
    (k.comp (reindexSpatialProjection e)) ν hν hO hx₀ hxk g hginfty
  refine ⟨V,hV,hxV,hVO,u,hu,?_⟩
  intro x hx
  exact (hug hx).trans (hext ⟨hx.1,hVO hx.2⟩)

end OAI.Analysis.PDE.Dirichlet
