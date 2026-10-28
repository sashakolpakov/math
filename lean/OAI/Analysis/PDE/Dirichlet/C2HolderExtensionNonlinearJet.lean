import OAI.Analysis.Normed.Function.Holder.C2HolderExtensionJets
import OAI.Analysis.PDE.Dirichlet.NonlinearParameterJetReindex

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

attribute [local instance] linearizedFirstGroup linearizedFirstSpace
  linearizedSecondGroup linearizedSecondSpace

variable {Z E W : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ} {U : Set Z}

/-- The spatial two-jet stored by the complete Dirichlet function space. -/
def storedNonlinearTwoJet (u : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (x : K) : NonlinearJet E :=
  ((x,OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative u x),OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative u x)

/-- A joint C² extension has the actual stored spatial jet at every point
of the closed domain, not merely in its interior. -/
theorem parameterJetProjection_joint_extension
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (u : Z → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    {g : Z × E → ℝ} (hg : ContDiff ℝ 2 g)
    (he : ∀ z ∈ U, ∀ x : K, g (z,x) = OAI.Analysis.Normed.Function.Holder.C2Holder.value (u z) x)
    {z : Z} (hz : z ∈ U) (x : K) :
    parameterJetProjection (ContinuousLinearMap.fst ℝ Z E)
      (ContinuousLinearMap.snd ℝ Z E) (ContinuousLinearMap.inr ℝ Z E)
      (nonlinearTwoJet g (z,x)) = (z,storedNonlinearTwoJet (u z) x) := by
  rw [parameterJetProjection_product_twoJet hg z (x:E)]
  obtain ⟨hD,hH⟩ := OAI.Analysis.Normed.Function.Holder.C2Holder.spatial_derivatives_of_joint_C2_extension
    hΩ hKΩ u hg he z hz x
  simp only [nonlinearTwoJet,storedNonlinearTwoJet,hD,hH]

/-- The same closed-domain identification in arbitrary linear coordinates,
including the Euclidean coordinates used by the boundary bootstrap. -/
theorem parameterJetProjection_reindex_joint_extension
    (e : W ≃L[ℝ] Z × E) (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (u : Z → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    {g : Z × E → ℝ} (hg : ContDiff ℝ 2 g)
    (he : ∀ z ∈ U, ∀ x : K, g (z,x) = OAI.Analysis.Normed.Function.Holder.C2Holder.value (u z) x)
    (w : W) (hz : (e w).1 ∈ U) (hx : (e w).2 ∈ K) :
    parameterJetProjection (reindexParameterProjection e) (reindexSpatialProjection e)
      (reindexSpatialInclusion e) (nonlinearTwoJet (fun y => g (e y)) w) =
      ((e w).1,storedNonlinearTwoJet (u (e w).1) ⟨(e w).2,hx⟩) := by
  rw [parameterJetProjection_reindex_ambient e hg w]
  exact parameterJetProjection_joint_extension hΩ hKΩ u hg he hz ⟨(e w).2,hx⟩

/-- A stored-jet equation is therefore an equation for the actual joint
C² extension, including the boundary and after Euclidean reindexing. -/
theorem parameterResidual_reindex_joint_extension
    (e : W ≃L[ℝ] Z × E) (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (u : Z → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (F : Z × NonlinearJet E → ℝ)
    {g : Z × E → ℝ} (hg : ContDiff ℝ 2 g)
    (he : ∀ z ∈ U, ∀ x : K, g (z,x) = OAI.Analysis.Normed.Function.Holder.C2Holder.value (u z) x)
    (hF : ∀ z ∈ U, ∀ x : K, F (z,storedNonlinearTwoJet (u z) x) = 0)
    (w : W) (hz : (e w).1 ∈ U) (hx : (e w).2 ∈ K) :
    parameterResidual (reindexParameterProjection e) (reindexSpatialProjection e)
      (reindexSpatialInclusion e) F (nonlinearTwoJet (fun y => g (e y)) w) = 0 := by
  change F (parameterJetProjection _ _ _ _) = 0
  rw [parameterJetProjection_reindex_joint_extension e hΩ hKΩ u hg he w hz hx]
  exact hF (e w).1 hz ⟨(e w).2,hx⟩

end OAI.Analysis.PDE.Dirichlet
