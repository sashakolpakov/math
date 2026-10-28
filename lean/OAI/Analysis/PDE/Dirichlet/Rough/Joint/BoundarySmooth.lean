import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.HalfspaceSmooth
import OAI.Analysis.PDE.Dirichlet.ParameterTangentJetReindex

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

/-- Combined parameter/tangent regularity and the actual spatial normal
equation make a genuine joint C² extension smooth up to the boundary.
The PDE is not required to be elliptic in the external parameters. -/
theorem contDiffOn_infty_joint_extension
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
        (0,k.smulRight k) ≠ 0) :
    ContDiffOn ℝ ∞ g ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O) := by
  exact contDiffOn_infty_parameter_halfspace_of_mixed_tangents
    (reindexParameterProjection e) (reindexSpatialProjection e) (reindexSpatialInclusion e)
    F hF (k.comp (reindexSpatialProjection e)) k (reindexNormal_comp_inclusion e k)
    ν hν hO hg hi
    (contDiffOn_tangent_jets_of_mixed_reindex e k hO hext hmaps hmixed) he hell

end OAI.Analysis.PDE.Dirichlet
