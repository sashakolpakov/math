import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.NormalClosed

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance closedNormalFirstGroup (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
local instance closedNormalFirstSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance closedNormalSecondGroup (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance closedNormalSecondSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_actual_fderiv {S : Set E} (hS : UniqueDiffOn ℝ S)
    {f : E → ℝ} {k : ℕ} (hf : ContDiffOn ℝ (k+1) f S)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    ContDiffOn ℝ k (fderiv ℝ f) S := by
  apply (hf.fderivWithin hS (by simp)).congr
  intro x hx
  exact (fderivWithin_eq_fderiv (hS x hx) (hd x hx)).symm

theorem contDiffOn_normalJetRemainder
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {S : Set E} (hS : UniqueDiffOn ℝ S) {f : E → ℝ} {k : ℕ}
    (hf : ∀ x ∈ S, ContDiffAt ℝ 2 f x)
    (ht : ∀ v, ℓ v = 0 → ContDiffOn ℝ (k+1) (constantDirectional f v) S) :
    ContDiffOn ℝ k (normalJetRemainder ℓ ν f) S := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  have hv : ℓ (v - ℓ v • ν) = 0 := by simp [hν]
  have hw : ℓ (w - ℓ w • ν) = 0 := by simp [hν]
  have hd (a : E) (x : E) (hx : x ∈ S) :
      DifferentiableAt ℝ (constantDirectional f a) x :=
    ((hf x hx).fderiv_right (m := 1) (by norm_num) |>.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have ha : ContDiffOn ℝ k (fun y ↦ fderiv ℝ (constantDirectional f (v - ℓ v • ν)) y w) S :=
    (contDiffOn_actual_fderiv hS (ht _ hv) (hd _)).clm_apply contDiffOn_const
  have hb : ContDiffOn ℝ k (fun y ↦ fderiv ℝ (constantDirectional f (w - ℓ w • ν)) y ν) S :=
    (contDiffOn_actual_fderiv hS (ht _ hw) (hd _)).clm_apply contDiffOn_const
  apply (ha.add (contDiffOn_const.mul hb)).congr
  intro y hy
  rw [normalJetRemainder_apply, fderiv_constantDirectional_apply (hf y hy),
    fderiv_constantDirectional_apply (hf y hy),
    ((hf y hy).isSymmSndFDerivAt (by norm_num)).eq (v - ℓ v • ν) w]

/-- Closed-domain nonlinear bootstrap. The only off-domain regularity used
is an initial C² representative, which finite reflection supplies from the
original C² closed jets. Higher derivatives are proved on the closed set. -/
theorem contDiffOn_of_nonlinear_equation_and_tangents
    (F : (E × (E →L[ℝ] ℝ)) × (E →L[ℝ] E →L[ℝ] ℝ) → ℝ)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {S : Set E} (hS : UniqueDiffOn ℝ S) {f : E → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ (k+1) f S) (hf2 : ∀ x ∈ S, ContDiffAt ℝ 2 f x)
    (ht : ∀ v, ℓ v = 0 → ContDiffOn ℝ (k+1) (constantDirectional f v) S)
    (hF : ∀ x ∈ S, ContDiffAt ℝ k F ((x,fderiv ℝ f x),fderiv ℝ (fderiv ℝ f) x))
    (he : ∀ x ∈ S, F ((x,fderiv ℝ f x),fderiv ℝ (fderiv ℝ f) x) = 0)
    (hell : ∀ x ∈ S, fderiv ℝ F ((x,fderiv ℝ f x),fderiv ℝ (fderiv ℝ f) x)
      (0,ℓ.smulRight ℓ) ≠ 0) :
    ContDiffOn ℝ (k+2) f S := by
  let R := normalJetRemainder ℓ ν f
  let u : E → ℝ := fun y ↦ fderiv ℝ (fderiv ℝ f) y ν ν
  have hsplit (y : E) : R y + u y • ℓ.smulRight ℓ = fderiv ℝ (fderiv ℝ f) y := by
    dsimp [R,u,normalJetRemainder]
    exact sub_add_cancel _ _
  have hR : ContDiffOn ℝ k R S := contDiffOn_normalJetRemainder ℓ ν hν hS hf2 ht
  have hD : ContDiffOn ℝ k (fderiv ℝ f) S := contDiffOn_actual_fderiv hS hf
    (fun x hx ↦ (hf2 x hx).differentiableAt (by norm_num))
  have hu : ContDiffOn ℝ k u S := by
    intro x hx
    apply contDiffWithinAt_normal_component F (fun y ↦ (y,fderiv ℝ f y)) R (ℓ.smulRight ℓ) u hk
    · simpa only [hsplit] using hF x hx
    · exact contDiffWithinAt_id.prodMk (hD x hx)
    · exact hR x hx
    · exact ((((hf2 x hx).fderiv_right (m := 1) (by norm_num)).fderiv_right
        (m := 0) (by norm_num)).continuousAt.clm_apply continuousAt_const).clm_apply
          continuousAt_const |>.continuousWithinAt
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [hsplit,he y hy,he x hx]
    · simpa only [hsplit] using hell x hx
  have hH : ContDiffOn ℝ k (fderiv ℝ (fderiv ℝ f)) S :=
    (hR.add (hu.smul contDiffOn_const)).congr (fun y _ ↦ (hsplit y).symm)
  have hD' : ContDiffOn ℝ (k+1) (fderiv ℝ f) S :=
    contDiffOn_succ_of_derivative_field k hH (fun x hx ↦
      ((hf2 x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num) |>.hasFDerivAt.hasFDerivWithinAt)
  exact contDiffOn_succ_of_derivative_field (k+1) hD' (fun x hx ↦
    (hf2 x hx).differentiableAt (by norm_num) |>.hasFDerivAt.hasFDerivWithinAt)

end OAI.Analysis.PDE.Dirichlet
