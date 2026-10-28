import OAI.Analysis.PDE.Dirichlet.Rough.Joint.GeometricHalfpatch
import OAI.Analysis.PDE.Dirichlet.CalculusJointChartMatrix

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

theorem exists_smooth_joint_physical_chart
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
    (k : X →L[ℝ] ℝ) (ν : X) (hν : k ν = 1) {c : ℝ} (hcpos : 0 < c)
    (hlevel : ∀ x ∈ ball (0:X) 1, r (G x) = -c * k x)
    (hPG : ∀ x ∈ ball (0:X) 1, (fun y => P' (G y)) =ᶠ[𝓝 x] id)
    (hGP : ∀ x ∈ ball (0:X) 1, (fun y => G (P' y)) =ᶠ[𝓝 (G x)] id)
    (ht : ParameterDeformation.HasJointGeometricSolutionFamiliesAt (T := k.ker) e b r f hΩK α p₀)
    (hf : ∀ p ∈ S₀, ∀ x, r x ≤ 0 → ContDiffAt ℝ 2 (fun y => f (p,y)) x)
    (Bg : Z × E → Phys →L[ℝ] Phys →L[ℝ] ℝ)
    (J : Z × E → Phys →L[ℝ] E)
    (T : Z × E → Phys →L[ℝ] Phys →L[ℝ] E) (load : Z × E → ℝ)
    (hBg : ContDiff ℝ ∞ Bg) (hJ : ContDiff ℝ ∞ J)
    (hT : ContDiff ℝ ∞ T) (hload : ContDiff ℝ ∞ load)
    (honto : ∀ p ∈ S₀, ∀ x, r x ≤ 0 → Function.Surjective (J (p,x)))
    (hpositive : ∀ p ∈ S₀, ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (mooreChartMatrix (Bg (p,x)) (J (p,x)) (T (p,x))
        (fderiv ℝ (fun y => f (p,y)) x)
        (fderiv ℝ (fderiv ℝ (fun y => f (p,y))) x))).PosDef)
    (heq : ∀ p ∈ S₀, ∀ x, r x ≤ 0 →
      OAI.LinearAlgebra.Moore.mooreDet n (mooreChartMatrix (Bg (p,x)) (J (p,x)) (T (p,x))
        (fderiv ℝ (fun y => f (p,y)) x)
        (fderiv ℝ (fderiv ℝ (fun y => f (p,y))) x)) = load (p,x))
    {a : E} (hPa : P' a = 0) {V₀ : Set E} (hV₀ : IsOpen V₀) (haV₀ : a ∈ V₀)
    (hGPinV : ∀ x ∈ V₀, G (P' x) = x) (hPV : MapsTo P' V₀ (ball 0 1)) :
    ∃ O : Set (Z × E), IsOpen O ∧ (p₀,a) ∈ O ∧
      ∃ u : Z × E → ℝ, ContDiff ℝ ∞ u ∧
        ∀ p ∈ O, r p.2 ≤ 0 → u p = f p := by
  have hside (x : X) (hx : x ∈ ball (0:X) 1) (hk : 0 ≤ k x) : r (G x) ≤ 0 := by
    rw [hlevel x hx]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcpos.le) hk
  have hmatrix (p : Z) (hp : p ∈ S₀) (x : X) (hx : x ∈ ball (0:X) 1) (hk : 0 ≤ k x) :=
    mooreChartMatrix_jointChart Bg J T (q := (p,x))
      (hf p hp (G x) (hside x hx hk)) (hG.contDiffAt.of_le (by simp))
      (hP.contDiffAt.of_le (by simp)) (hPG x hx).eq_of_nhds (hGP x hx)
  dsimp only [Function.comp_def] at hmatrix
  obtain ⟨O,hO,hpO,u,hu,hue⟩ := ParameterDeformation.exists_smooth_joint_geometric_halfpatch e b r hr hrp hreg
    hclosure hΩK α f hS₀ hp₀ hc hinterior j G P' hG hP
    (hPG 0 (mem_ball_self zero_lt_one)) k ν hν hcpos hlevel ht hf
    (jointChartBackground G Bg) (jointChartJacobian P' G J)
    (jointChartCurvature P' G J T) (jointChartLoad G load)
    (contDiff_jointChartBackground hG hBg) (contDiff_jointChartJacobian hP hG hJ)
    (contDiff_jointChartCurvature hP hG hJ hT) (contDiff_jointChartLoad hG hload)
    (fun p hp x hx hk => jointChartJacobian_surjective J
      (hG.differentiable (by simp) x) (hP.differentiable (by simp) (G x))
      (hPG x hx) (honto p hp (G x) (hside x hx hk)))
    (fun p hp x hx hk => by
      rw [hmatrix p hp x hx hk]
      exact hpositive p hp (G x) (hside x hx hk))
    (fun p hp x hx hk => by
      rw [hmatrix p hp x hx hk]
      exact heq p hp (G x) (hside x hx hk))
  let H : Z × E → Z × X := fun p => (p.1,P' p.2)
  have hH : ContDiff ℝ ∞ H := contDiff_fst.prodMk (hP.comp contDiff_snd)
  refine ⟨(H ⁻¹' O) ∩ (univ ×ˢ V₀),(hO.preimage hH.continuous).inter (isOpen_univ.prod hV₀),
    ⟨?_,⟨mem_univ _,haV₀⟩⟩,fun p => u (H p),hu.comp hH,?_⟩
  · change (p₀,P' a) ∈ O
    simpa only [hPa] using hpO
  · intro p hp hpr
    have he : r p.2 = -c * k (P' p.2) := by
      exact (congrArg r (hGPinV p.2 hp.2.2)).symm.trans
        (hlevel (P' p.2) (hPV hp.2.2))
    have hk : 0 ≤ k (P' p.2) := by nlinarith
    exact (hue (H p) hp.1 hk).trans (congrArg (fun x => f (p.1,x)) (hGPinV p.2 hp.2.2))

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
