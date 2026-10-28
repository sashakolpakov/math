import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.NormalBootstrap
import OAI.Analysis.PDE.Dirichlet.Closed.DerivativeTrace

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E Z H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- The implicit formula remains valid on a closed set. In particular this
does not presume any derivative on the other side of the boundary. -/
theorem contDiffWithinAt_of_continuous_implicit_equation
    (Q : Z × ℝ → ℝ) (b : E → Z) (u : E → ℝ) {S : Set E} {x : E} {q : ℕ∞ω}
    (hQ : ContDiffAt ℝ q Q (b x,u x)) (hq : q ≠ 0)
    (hD : ((fderiv ℝ Q (b x,u x)).comp (ContinuousLinearMap.inr ℝ Z ℝ)).IsInvertible)
    (hb : ContDiffWithinAt ℝ q b S x) (hu : ContinuousWithinAt u S x)
    (he : ∀ᶠ y in 𝓝[S] x, Q (b y,u y) = Q (b x,u x)) :
    ContDiffWithinAt ℝ q u S x := by
  let g : Z → ℝ := hQ.implicitFunction hq hD
  have hg : ContDiffAt ℝ q g (b x) := hQ.contDiffAt_implicitFunction hq hD
  have ht : Tendsto (fun y ↦ (b y,u y)) (𝓝[S] x) (𝓝 (b x,u x)) :=
    hb.continuousWithinAt.prodMk hu
  have hiff := ht.eventually (hQ.eventually_apply_eq_iff_implicitFunction hq hD)
  have heq : u =ᶠ[𝓝[S] x] (fun y ↦ g (b y)) := by
    filter_upwards [he,hiff] with y hy hiy
    exact (hiy.mp hy).symm
  apply (hg.comp_contDiffWithinAt x hb).congr_of_eventuallyEq heq
  exact (hQ.implicitFunction_apply_self hq hD).symm

theorem contDiffWithinAt_normal_component
    (F : Z × H → ℝ) (b : E → Z) (R : E → H) (N : H) (u : E → ℝ)
    {S : Set E} {x : E} {k : ℕ} (hk : 1 ≤ k)
    (hF : ContDiffAt ℝ k F (b x,R x + u x • N))
    (hb : ContDiffWithinAt ℝ k b S x) (hR : ContDiffWithinAt ℝ k R S x)
    (hu : ContinuousWithinAt u S x)
    (he : ∀ᶠ y in 𝓝[S] x, F (b y,R y + u y • N) = F (b x,R x + u x • N))
    (hell : fderiv ℝ F (b x,R x + u x • N) (0,N) ≠ 0) :
    ContDiffWithinAt ℝ k u S x := by
  let Q : (Z × H) × ℝ → ℝ := fun p ↦ F (p.1.1,p.1.2 + p.2 • N)
  have hQ : ContDiffAt ℝ k Q ((b x,R x),u x) := hF.comp ((b x,R x),u x)
    ((contDiffAt_fst.fst).prodMk
      (contDiffAt_fst.snd.add (contDiffAt_snd.smul contDiffAt_const)))
  have hk' : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hs : HasDerivAt (fun t : ℝ ↦ F (b x,R x + t • N))
      (fderiv ℝ F (b x,R x + u x • N) (0,N)) (u x) := by
    apply (hF.differentiableAt hk').hasFDerivAt.comp_hasDerivAt
    simpa only [one_smul,zero_add,Pi.add_apply,id_eq] using
      (hasDerivAt_const (u x) (b x)).prodMk
        ((hasDerivAt_const (u x) (R x)).add ((hasDerivAt_id (u x)).smul_const N))
  have hD : ((fderiv ℝ Q ((b x,R x),u x)).comp
      (ContinuousLinearMap.inr ℝ (Z × H) ℝ)).IsInvertible := by
    rw [← fderiv_second_variable (hQ.differentiableAt hk')]
    apply scalar_clm_isInvertible
    change fderiv ℝ (fun t : ℝ ↦ F (b x,R x + t • N)) (u x) 1 ≠ 0
    rw [hs.hasFDerivAt.fderiv]
    simpa only [ContinuousLinearMap.toSpanSingleton_apply,one_smul] using hell
  exact contDiffWithinAt_of_continuous_implicit_equation Q (fun y ↦ (b y,R y)) u
    hQ hk' hD (hb.prodMk hR) hu he

end OAI.Analysis.PDE.Dirichlet
