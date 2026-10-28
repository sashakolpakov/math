import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Finite Rank -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteRank.Constructions.FiniteRankChart

noncomputable section

/-!
# RiemannProjectivity: finite fibers in a chart of maximal derivative rank

If a projected map is the first coordinate and its derivative already has
maximal allowed rank, all derivatives in the remaining coordinates vanish.
A nontrivial remaining coordinate space would produce an infinite fiber.
-/

open Set Filter _root_.Module _root_.Metric
open scoped _root_.Topology

variable {V W R K : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup R] [NormedSpace ℂ R] [FiniteDimensional ℂ R]
  [NormedAddCommGroup K] [NormedSpace ℂ K] [FiniteDimensional ℂ K]

omit [FiniteDimensional ℂ W] [FiniteDimensional ℂ R] in
theorem ker_eq_of_projected_rank (A : V →L[ℂ] W) (P : W →L[ℂ] R)
    (hsurj : Function.Surjective (P.comp A)) (hrank : finrank ℂ A.range ≤ finrank ℂ R) :
    A.ker = (P.comp A).ker := by
  apply Submodule.eq_of_le_of_finrank_le
  · intro v hv
    change P (A v) = 0
    rw [show A v = 0 from hv, map_zero]
  · have hA := A.toLinearMap.finrank_range_add_finrank_ker
    have hP := (P.comp A).toLinearMap.finrank_range_add_finrank_ker
    have htop : (P.comp A).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have hrange : finrank ℂ (P.comp A).range = finrank ℂ R := by rw [htop]; simp
    change finrank ℂ A.range + finrank ℂ A.ker = finrank ℂ V at hA
    change finrank ℂ (P.comp A).range + finrank ℂ (P.comp A).ker = finrank ℂ V at hP
    omega

omit [FiniteDimensional ℂ W] in
theorem subsingleton_vertical_of_finite_fiber
    {H : R × K → W} {O : Set (R × K)} (hO : IsOpen O)
    (hH : DifferentiableOn ℂ H O) (P : W →L[ℂ] R)
    (hfirst : ∀ p ∈ O, P (H p) = p.1)
    (hrank : ∀ p ∈ O, finrank ℂ (fderiv ℂ H p).range ≤ finrank ℂ R)
    {p : R × K} (hp : p ∈ O)
    (hfinite : {z : R × K | z ∈ O ∧ H z = H p}.Finite) : Subsingleton K := by
  by_contra hK
  let : Nontrivial K := not_subsingleton_iff_nontrivial.mp hK
  let B : Set K := (fun u : K => (p.1, u)) ⁻¹' O
  have hB : IsOpen B := hO.preimage (continuous_const.prodMk continuous_id)
  have hpB : p.2 ∈ B := hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hB p.2 hpB
  let b : K → W := fun u => H (p.1, u)
  have hbd : DifferentiableOn ℂ b B := hH.comp
    ((differentiable_const p.1).prodMk differentiable_id).differentiableOn
    (mapsTo_preimage (fun u : K => (p.1, u)) O)
  have hzero : ∀ u ∈ B, fderiv ℂ b u = 0 := by
    intro u hu
    have hHu := hH.differentiableAt (hO.mem_nhds hu)
    have heq : (fun z => P (H z)) =ᶠ[𝓝 (p.1, u)] Prod.fst :=
      mem_of_superset (hO.mem_nhds hu) (fun z hz => hfirst z hz)
    have hD : P.comp (fderiv ℂ H (p.1, u)) = ContinuousLinearMap.fst ℂ R K := by
      rw [← (P.hasFDerivAt.comp (p.1, u) hHu.hasFDerivAt).fderiv]
      change fderiv ℂ (fun z => P (H z)) (p.1, u) = _
      rw [heq.fderiv_eq]
      exact (hasFDerivAt_fst (𝕜 := ℂ) (p := (p.1, u))).fderiv
    have hsurj : Function.Surjective (P.comp (fderiv ℂ H (p.1, u))) := by
      rw [hD]
      exact Prod.fst_surjective
    have hker := ker_eq_of_projected_rank (fderiv ℂ H (p.1, u)) P hsurj (hrank _ hu)
    have hi : HasFDerivAt (fun v : K => (p.1, v)) (ContinuousLinearMap.inr ℂ R K) u :=
      (hasFDerivAt_const p.1 u).prodMk (hasFDerivAt_id u)
    have hb := hHu.hasFDerivAt.comp u hi
    rw [show fderiv ℂ b u = (fderiv ℂ H (p.1, u)).comp (ContinuousLinearMap.inr ℂ R K)
      from hb.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    change (ContinuousLinearMap.inr ℂ R K v) ∈ (fderiv ℂ H (p.1, u)).ker
    rw [hker, hD]
    rfl
  have hconst : ∀ u ∈ Metric.ball p.2 r, b u = H p := by
    intro u hu
    exact isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball p.2 r).isPreconnected
      (hbd.mono hball) (fun z hz => hzero z (hball hz)) hu (Metric.mem_ball_self hr)
  have hinj : Function.Injective (fun u : K => (p.1, u)) :=
    fun a b hab => congrArg Prod.snd hab
  have hfball : (Metric.ball p.2 r).Finite :=
    (hfinite.preimage hinj.injOn).subset (fun u hu => ⟨hball hu, hconst u hu⟩)
  exact (infinite_of_mem_nhds p.2 (Metric.ball_mem_nhds p.2 hr)) hfball

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteRank.Constructions.FiniteRankChart
