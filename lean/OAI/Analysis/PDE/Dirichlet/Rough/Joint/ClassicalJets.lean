import OAI.Analysis.PDE.Dirichlet.NonlinearParameterJetReindex

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

attribute [local instance] linearizedFirstGroup linearizedFirstSpace
  linearizedSecondGroup linearizedSecondSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The comparison is local at the closed domain; no control of an
arbitrary classical extension away from it is required. -/
theorem derivatives_eq_on_dense_closed_domain_at
    {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) (hKΩ : K ⊆ closure Ω)
    {f g : E → ℝ} (hf : ∀ x ∈ K, ContDiffAt ℝ 2 f x)
    (hg : ∀ x ∈ K, ContDiffAt ℝ 2 g x) (he : EqOn f g K) :
    ∀ x ∈ K, fderiv ℝ f x = fderiv ℝ g x ∧
      fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ g) x := by
  have hlocal (x : E) (hx : x ∈ Ω) : f =ᶠ[𝓝 x] g := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact he (hΩK hy)
  have hD : EqOn (fderiv ℝ f) (fderiv ℝ g) Ω := fun x hx => (hlocal x hx).fderiv_eq
  have hH : EqOn (fderiv ℝ (fderiv ℝ f)) (fderiv ℝ (fderiv ℝ g)) Ω := by
    intro x hx
    have hDlocal : fderiv ℝ f =ᶠ[𝓝 x] fderiv ℝ g := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact hD hy
    exact hDlocal.fderiv_eq
  have hfD : ContinuousOn (fderiv ℝ f) K := fun x hx =>
    ((hf x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hgD : ContinuousOn (fderiv ℝ g) K := fun x hx =>
    ((hg x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hfH : ContinuousOn (fderiv ℝ (fderiv ℝ f)) K := fun x hx =>
    (((hf x hx).fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv
      (by norm_num)).continuousWithinAt
  have hgH : ContinuousOn (fderiv ℝ (fderiv ℝ g)) K := fun x hx =>
    (((hg x hx).fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv
      (by norm_num)).continuousWithinAt
  have hDK := hD.of_subset_closure hfD hgD hΩK hKΩ
  have hHK := hH.of_subset_closure hfH hgH hΩK hKΩ
  exact fun x hx => ⟨hDK hx,hHK hx⟩

/-- A C² representative has the same two-jet as any classical function
with the same values on a closed domain whose interior is dense. -/
theorem derivatives_eq_on_dense_closed_domain
    {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) (hKΩ : K ⊆ closure Ω)
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : EqOn f g K) :
    ∀ x ∈ K, fderiv ℝ f x = fderiv ℝ g x ∧
      fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ g) x := by
  have hlocal (x : E) (hx : x ∈ Ω) : f =ᶠ[𝓝 x] g := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact he (hΩK hy)
  have hD : EqOn (fderiv ℝ f) (fderiv ℝ g) Ω := fun x hx => (hlocal x hx).fderiv_eq
  have hH : EqOn (fderiv ℝ (fderiv ℝ f)) (fderiv ℝ (fderiv ℝ g)) Ω := by
    intro x hx
    have hDlocal : fderiv ℝ f =ᶠ[𝓝 x] fderiv ℝ g := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact hD hy
    exact hDlocal.fderiv_eq
  have hfD : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgD : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hfH : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) := hfD.fderiv_right (by norm_num)
  have hgH : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ g)) := hgD.fderiv_right (by norm_num)
  have hDK := hD.of_subset_closure hfD.continuous.continuousOn
    hgD.continuous.continuousOn hΩK hKΩ
  have hHK := hH.of_subset_closure hfH.continuous.continuousOn
    hgH.continuous.continuousOn hΩK hKΩ
  exact fun x hx => ⟨hDK hx,hHK hx⟩

variable {Z W : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The projected jet of a joint C² extension agrees with the actual
classical spatial jet of an independently chosen family. No parameter
regularity of that chosen family is assumed. -/
theorem parameterJetProjection_of_classical_family
    (e : W ≃L[ℝ] Z × E) {Ω K : Set E} {S : Set Z}
    (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) (hKΩ : K ⊆ closure Ω)
    {F : Z × E → ℝ} (hF : ∀ z ∈ S, ContDiff ℝ 2 (fun x => F (z,x)))
    {g : W → ℝ} (hg : ContDiff ℝ 2 g)
    (he : ∀ z ∈ S, ∀ x ∈ K, g (e.symm (z,x)) = F (z,x))
    (w : W) (hz : (e w).1 ∈ S) (hx : (e w).2 ∈ K) :
    parameterJetProjection (reindexParameterProjection e) (reindexSpatialProjection e)
      (reindexSpatialInclusion e) (nonlinearTwoJet g w) =
        ((e w).1,nonlinearTwoJet (fun x => F ((e w).1,x)) (e w).2) := by
  have hprod : ContDiff ℝ 2 (fun p : Z × E => g (e.symm p)) := hg.comp e.symm.contDiff
  have hp := parameterJetProjection_reindex_twoJet e hprod w
  have hcomp : (fun y : W => g (e.symm (e y))) = g := by
    funext y
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hcomp] at hp
  have hslice : ContDiff ℝ 2 (fun x : E => g (e.symm ((e w).1,x))) :=
    hprod.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨hD,hH⟩ := derivatives_eq_on_dense_closed_domain hΩ hΩK hKΩ
    hslice (hF (e w).1 hz) (he (e w).1 hz) (e w).2 hx
  simpa only [nonlinearTwoJet,hD,hH] using hp

/-- Local spatial smoothness near the closed fiber suffices for the exact
projected-jet identity. In particular no global transport extension is needed. -/
theorem parameterJetProjection_of_classical_family_at
    (e : W ≃L[ℝ] Z × E) {Ω K : Set E} {S : Set Z}
    (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) (hKΩ : K ⊆ closure Ω)
    {F : Z × E → ℝ}
    (hF : ∀ z ∈ S, ∀ x ∈ K, ContDiffAt ℝ 2 (fun y => F (z,y)) x)
    {g : W → ℝ} (hg : ContDiff ℝ 2 g)
    (he : ∀ z ∈ S, ∀ x ∈ K, g (e.symm (z,x)) = F (z,x))
    (w : W) (hz : (e w).1 ∈ S) (hx : (e w).2 ∈ K) :
    parameterJetProjection (reindexParameterProjection e) (reindexSpatialProjection e)
      (reindexSpatialInclusion e) (nonlinearTwoJet g w) =
        ((e w).1,nonlinearTwoJet (fun x => F ((e w).1,x)) (e w).2) := by
  have hprod : ContDiff ℝ 2 (fun p : Z × E => g (e.symm p)) := hg.comp e.symm.contDiff
  have hp := parameterJetProjection_reindex_twoJet e hprod w
  have hcomp : (fun y : W => g (e.symm (e y))) = g := by
    funext y
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hcomp] at hp
  have hslice : ContDiff ℝ 2 (fun x : E => g (e.symm ((e w).1,x))) :=
    hprod.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨hD,hH⟩ := derivatives_eq_on_dense_closed_domain_at hΩ hΩK hKΩ
    (fun _ _ => hslice.contDiffAt) (hF (e w).1 hz) (he (e w).1 hz) (e w).2 hx
  simpa only [nonlinearTwoJet,hD,hH] using hp

end OAI.Analysis.PDE.Dirichlet
