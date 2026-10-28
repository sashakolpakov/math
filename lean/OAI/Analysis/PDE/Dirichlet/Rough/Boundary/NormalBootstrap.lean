import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.NormalImplicit
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.NormalJet

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

theorem scalar_clm_isInvertible (L : ℝ →L[ℝ] ℝ) (hL : L 1 ≠ 0) :
    L.IsInvertible := by
  have he (t : ℝ) : L t = t * L 1 := by
    simpa only [smul_eq_mul, mul_one] using L.map_smul t (1 : ℝ)
  have hi : Function.Injective L := by
    intro a b hab
    rw [he a, he b] at hab
    exact mul_right_cancel₀ hL hab
  have hs : Function.Surjective L := by
    intro y
    refine ⟨y / L 1, ?_⟩
    rw [he, div_mul_cancel₀ _ hL]
  exact ⟨ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs), rfl⟩

variable {E Z H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

local instance bootstrapFirstGroup (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
local instance bootstrapFirstSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance bootstrapSecondGroup (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance bootstrapSecondSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance

theorem fderiv_second_variable {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Q : P × X → Y} {p : P} {x : X} (hQ : DifferentiableAt ℝ Q (p,x)) :
    fderiv ℝ (fun y ↦ Q (p,y)) x =
      (fderiv ℝ Q (p,x)).comp (ContinuousLinearMap.inr ℝ P X) := by
  have hi : HasFDerivAt (fun y : X ↦ (p,y)) (ContinuousLinearMap.inr ℝ P X) x := by
    change HasFDerivAt (fun y : X ↦ (p,y))
      ((0 : X →L[ℝ] P).prod (ContinuousLinearMap.id ℝ X)) x
    simpa only [id_eq] using (hasFDerivAt_const p x).prodMk (hasFDerivAt_id x)
  exact (hQ.hasFDerivAt.comp x hi).fderiv

/-- Scalar ellipticity in the missing component suffices for a continuous
solution of the nonlinear equation to inherit the regularity of all the
other components. The candidate itself is not assumed differentiable. -/
theorem contDiffAt_normal_component
    (F : Z × H → ℝ) (b : E → Z) (R : E → H) (N : H) (u : E → ℝ)
    {x : E} {k : ℕ} (hk : 1 ≤ k)
    (hF : ContDiffAt ℝ k F (b x, R x + u x • N))
    (hb : ContDiffAt ℝ k b x) (hR : ContDiffAt ℝ k R x)
    (hu : ContinuousAt u x)
    (he : ∀ᶠ y in 𝓝 x, F (b y, R y + u y • N) = F (b x, R x + u x • N))
    (hell : fderiv ℝ F (b x, R x + u x • N) (0,N) ≠ 0) :
    ContDiffAt ℝ k u x := by
  let Q : E × ℝ → ℝ := fun p ↦ F (b p.1, R p.1 + p.2 • N)
  have hQ : ContDiffAt ℝ k Q (x,u x) := hF.comp (x,u x)
    ((hb.comp (x,u x) contDiffAt_fst).prodMk
      ((hR.comp (x,u x) contDiffAt_fst).add (contDiffAt_snd.smul contDiffAt_const)))
  have hk' : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hs : HasDerivAt (fun t : ℝ ↦ F (b x, R x + t • N))
      (fderiv ℝ F (b x, R x + u x • N) (0,N)) (u x) := by
    apply (hF.differentiableAt hk').hasFDerivAt.comp_hasDerivAt
    simpa only [one_smul, zero_add, Pi.add_apply, id_eq] using
      (hasDerivAt_const (u x) (b x)).prodMk
        ((hasDerivAt_const (u x) (R x)).add ((hasDerivAt_id (u x)).smul_const N))
  have hD : ((fderiv ℝ Q (x,u x)).comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    rw [← fderiv_second_variable (hQ.differentiableAt hk')]
    apply scalar_clm_isInvertible
    change fderiv ℝ (fun t : ℝ ↦ F (b x, R x + t • N)) (u x) 1 ≠ 0
    rw [hs.hasFDerivAt.fderiv]
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hell
  exact contDiffAt_of_continuous_implicit_equation Q u hQ (by exact_mod_cast (by omega : k ≠ 0)) hD hu he

/-- Nonlinear recovery of all normal derivatives. Tangential regularity and
ellipticity determine the missing pure-normal Hessian component; there is no
assumption of higher differentiability in the normal direction. -/
theorem contDiffAt_of_nonlinear_equation_and_tangents [FiniteDimensional ℝ E]
    (F : (E × (E →L[ℝ] ℝ)) × (E →L[ℝ] E →L[ℝ] ℝ) → ℝ)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {f : E → ℝ} {x : E} {k : ℕ} (hk : 1 ≤ k)
    (hf : ContDiffAt ℝ (k+1) f x)
    (ht : ∀ v, ℓ v = 0 → ContDiffAt ℝ (k+1) (constantDirectional f v) x)
    (hF : ContDiffAt ℝ k F ((x,fderiv ℝ f x),fderiv ℝ (fderiv ℝ f) x))
    (he : ∀ᶠ y in 𝓝 x, F ((y,fderiv ℝ f y),fderiv ℝ (fderiv ℝ f) y) =
      F ((x,fderiv ℝ f x),fderiv ℝ (fderiv ℝ f) x))
    (hell : fderiv ℝ F ((x,fderiv ℝ f x),fderiv ℝ (fderiv ℝ f) x)
      (0,ℓ.smulRight ℓ) ≠ 0) :
    ContDiffAt ℝ (k+2) f x := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by exact_mod_cast (by omega : 2 ≤ k+1))
  let R := normalJetRemainder ℓ ν f
  let u : E → ℝ := fun y ↦ fderiv ℝ (fderiv ℝ f) y ν ν
  have hsplit (y : E) : R y + u y • ℓ.smulRight ℓ = fderiv ℝ (fderiv ℝ f) y := by
    dsimp [R,u,normalJetRemainder]
    exact sub_add_cancel _ _
  have hR : ContDiffAt ℝ k R x := contDiffAt_normalJetRemainder ℓ ν hν hf2 ht
  have hu : ContinuousAt u x :=
    (((hf2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
      continuousAt_const).clm_apply continuousAt_const
  have hub : ContDiffAt ℝ k u x := by
    apply contDiffAt_normal_component F (fun y ↦ (y,fderiv ℝ f y)) R (ℓ.smulRight ℓ) u hk
    · simpa only [hsplit] using hF
    · exact contDiffAt_id.prodMk (hf.fderiv_right (by simp))
    · exact hR
    · exact hu
    · simpa only [hsplit] using he
    · simpa only [hsplit] using hell
  apply contDiffAt_of_hessian_field hf2
  have hD := hR.add (hub.smul (contDiffAt_const (c := ℓ.smulRight ℓ)))
  exact hD.congr_of_eventuallyEq (Eventually.of_forall (fun y ↦ (hsplit y).symm))

end OAI.Analysis.PDE.Dirichlet
