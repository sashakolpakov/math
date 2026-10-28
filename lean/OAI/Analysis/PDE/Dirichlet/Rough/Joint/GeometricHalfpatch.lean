import OAI.Analysis.PDE.Dirichlet.Rough.Joint.ClassicalHalfpatch
import OAI.Analysis.PDE.Dirichlet.Rough.Joint.C2Extension

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

attribute [local instance] linearizedFirstGroup linearizedFirstSpace
  linearizedSecondGroup linearizedSecondSpace
attribute [local instance] residualFirstGroup residualFirstSpace
  residualSecondGroup residualSecondSpace

variable {n : ℕ} {Z E X P V ι : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "Phys" => CoordinateSpace n 4

/-- Combined geometric families give a genuinely smooth joint local
representative at a boundary chart. The equation is the actual classical
slice equation; no joint regularity of those slices is presupposed. -/
theorem exists_smooth_joint_geometric_halfpatch
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (r : E → ℝ)
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}) (α : ℝ)
    (f : Z × E → ℝ) {S₀ : Set Z} (hS₀ : IsOpen S₀) {p₀ : Z} (hp₀ : p₀ ∈ S₀)
    (hc : ParameterDeformation.HasJointGeometricSolutionFamiliesAt (T := E) e b r f hΩK α p₀)
    (hinterior : ∀ p ∈ S₀, ∀ x, r x < 0 → ContDiffAt ℝ ∞ f (p,x))
    (j : X ≃ₗᵢ[ℝ] E) (G : X → E) (P' : E → X)
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P')
    (hinv : (fun x => P' (G x)) =ᶠ[𝓝 (0:X)] id)
    (k : X →L[ℝ] ℝ) (ν : X) (hν : k ν = 1) {c : ℝ} (hcpos : 0 < c)
    (hlevel : ∀ x ∈ ball (0:X) 1, r (G x) = -c * k x)
    (ht : ParameterDeformation.HasJointGeometricSolutionFamiliesAt (T := k.ker) e b r f hΩK α p₀)
    (hf : ∀ p ∈ S₀, ∀ x, r x ≤ 0 → ContDiffAt ℝ 2 (fun y => f (p,y)) x)
    (Bg : Z × X → Phys →L[ℝ] Phys →L[ℝ] ℝ)
    (J : Z × X → Phys →L[ℝ] X)
    (T : Z × X → Phys →L[ℝ] Phys →L[ℝ] X) (load : Z × X → ℝ)
    (hBg : ContDiff ℝ ∞ Bg) (hJ : ContDiff ℝ ∞ J)
    (hT : ContDiff ℝ ∞ T) (hload : ContDiff ℝ ∞ load)
    (honto : ∀ p ∈ S₀, ∀ x ∈ ball (0:X) 1, 0 ≤ k x → Function.Surjective (J (p,x)))
    (hpositive : ∀ p ∈ S₀, ∀ x ∈ ball (0:X) 1, 0 ≤ k x →
      (OAI.LinearAlgebra.Moore.complexify (mooreChartMatrix (Bg (p,x)) (J (p,x)) (T (p,x))
        (fderiv ℝ (fun y => f (p,G y)) x)
        (fderiv ℝ (fderiv ℝ (fun y => f (p,G y))) x))).PosDef)
    (heq : ∀ p ∈ S₀, ∀ x ∈ ball (0:X) 1, 0 ≤ k x →
      OAI.LinearAlgebra.Moore.mooreDet n (mooreChartMatrix (Bg (p,x)) (J (p,x)) (T (p,x))
        (fderiv ℝ (fun y => f (p,G y)) x)
        (fderiv ℝ (fderiv ℝ (fun y => f (p,G y))) x)) = load (p,x)) :
    ∃ O : Set (Z × X), IsOpen O ∧ (p₀,(0:X)) ∈ O ∧
      ∃ u : Z × X → ℝ, ContDiff ℝ ∞ u ∧
        ∀ p ∈ O, 0 ≤ k p.2 → u p = f (p.1,G p.2) := by
  have hGQ : MapsTo G ({x | 0 ≤ k x} ∩ ball (0:X) 1) {x | r x ≤ 0} := by
    intro x hx
    change r (G x) ≤ 0
    rw [hlevel x hx.2]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcpos.le) hx.1
  obtain ⟨S₁,hS₁,hp₁,O₁,hO₁,h0₁,hmix⟩ :=
    ht.all_joint_mixed_chart_orders (hr.of_le (by simp)) hrp hreg j G P' hG hP hinv
      ((-c) • k) 0 (by
        intro x hx
        simpa only [zero_add,smul_apply,smul_eq_mul] using hlevel x hx)
      k.ker.subtypeL (by
        intro v
        change (-c) * k (v:X) = 0
        exact mul_eq_zero_of_right _ (show k (v:X) = 0 from v.property)) hGQ
  obtain ⟨S₂,hS₂,hp₂,g,hg,hge⟩ := hc.exists_joint_C2_extension hr hreg
  let S : Set Z := (S₀ ∩ S₁) ∩ S₂
  have hS : IsOpen S := (hS₀.inter hS₁).inter hS₂
  have hpS : p₀ ∈ S := ⟨⟨hp₀,hp₁⟩,hp₂⟩
  let Q : Set (Z × X) := S ×ˢ (({x | 0 ≤ k x} ∩ ball (0:X) 1) ∩ O₁)
  let d := Module.finrank ℝ (Z × X)
  let L : EuclideanSpace ℝ (Fin d) ≃L[ℝ] Z × X :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [d])
  let O : Set (EuclideanSpace ℝ (Fin d)) := L ⁻¹' (S ×ˢ (ball (0:X) 1 ∩ O₁))
  have hO : IsOpen O := (hS.prod (isOpen_ball.inter hO₁)).preimage L.continuous
  have hpO : L.symm (p₀,0) ∈ O := by
    change (L (L.symm (p₀,(0:X)))).1 ∈ S ∧
      (L (L.symm (p₀,(0:X)))).2 ∈ ball (0:X) 1 ∩ O₁
    rw [L.apply_symm_apply]
    exact ⟨hpS,⟨mem_ball_self zero_lt_one,h0₁⟩⟩
  have hnormal : (k.comp (reindexSpatialProjection L)) (L.symm (0,ν)) = 1 := by
    change k (L (L.symm (0,ν))).2 = 1
    simpa only [L.apply_symm_apply] using hν
  have hzero : (k.comp (reindexSpatialProjection L)) (L.symm (p₀,0)) = 0 := by
    change k (L (L.symm (p₀,0))).2 = 0
    simp only [L.apply_symm_apply,map_zero]
  have hmaps : MapsTo L ({x | 0 ≤ (k.comp (reindexSpatialProjection L)) x} ∩ O) Q := by
    intro x hx
    exact ⟨hx.2.1,⟨⟨hx.1,hx.2.2.1⟩,hx.2.2.2⟩⟩
  have hQ : ∀ p ∈ Q, p.1 ∈ S ∧ G p.2 ∈ {x | r x ≤ 0} := by
    intro p hp
    exact ⟨hp.1,hGQ hp.2.1⟩
  have hinner : ∀ x ∈ O, 0 < (k.comp (reindexSpatialProjection L)) x →
      ContDiffAt ℝ ∞ (fun y => f ((L y).1,G (L y).2)) x := by
    intro x hx hpos
    have hneg : r (G (L x).2) < 0 := by
      rw [hlevel _ hx.2.1]
      exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hcpos) hpos
    exact (hinterior (L x).1 hx.1.1.1 _ hneg).comp x
      ((contDiff_fst.prodMk (hG.comp contDiff_snd)).comp L.contDiff).contDiffAt
  have hmixed : ∀ (N : ℕ) (v : Fin N → Z × k.ker),
      ContDiffOn ℝ 2 (fun p : Z × X => iteratedFDeriv ℝ N
        (fun t : Z × k.ker => f (p.1+t.1,G (p.2+(t.2:X)))) 0 v) Q := by
    intro N v
    exact (hmix N v).mono (fun p hp => ⟨hp.1.1.2,hp.2⟩)
  obtain ⟨O',hO',hpO',hO'O,u,hu,hue⟩ := exists_smooth_joint_classical_halfpatch L k
    Bg J T load hBg hJ hT hload (L.symm (0,ν)) hnormal
    (isOpen_lt hr.continuous continuous_const) hΩK hclosure
    (fun p hp x hx => hf p hp.1.1 x hx) hg
    (fun p hp x hx => hge p hp.2 x hx) G hG hO hmaps hQ hinner hmixed
    (fun p hp => honto p.1 hp.1.1.1 p.2 hp.2.1.2 hp.2.1.1)
    (fun p hp => hpositive p.1 hp.1.1.1 p.2 hp.2.1.2 hp.2.1.1)
    (fun p hp => heq p.1 hp.1.1.1 p.2 hp.2.1.2 hp.2.1.1) hpO hzero
  refine ⟨L.symm ⁻¹' O',hO'.preimage L.symm.continuous,hpO',
    fun p => u (L.symm p),hu.comp L.symm.contDiff,?_⟩
  intro p hp hkp
  have hkh : 0 ≤ (k.comp (reindexSpatialProjection L)) (L.symm p) := by
    change 0 ≤ k (L (L.symm p)).2
    simpa only [L.apply_symm_apply] using hkp
  simpa only [L.apply_symm_apply] using hue ⟨hkh,hp⟩

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
