import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

/-! # Intrinsic Ball Topology -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic

noncomputable section

/-! Connectedness of the actual affine two-ball and uniqueness of a
continuous square-root comparison after fixing its value at one point. -/

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

def origin : Adelic.BallNatural.Ball := ⟨0, by norm_num [Adelic.BallNatural.Ball]⟩

theorem ballDomain_starConvex : StarConvex ℝ (0 : Fin 2 → ℂ) Adelic.BallGeometryData.ballDomain := by
  intro y hy a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have hb2 : b * b ≤ 1 := by nlinarith
  have hn : 0 ≤ Complex.normSq (y 0) + Complex.normSq (y 1) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  change Complex.normSq (y 0) + Complex.normSq (y 1) < 1 at hy
  change Complex.normSq ((a • (0 : Fin 2 → ℂ) + b • y) 0) +
    Complex.normSq ((a • (0 : Fin 2 → ℂ) + b • y) 1) < 1
  simp only [smul_zero, zero_add, Pi.smul_apply, Complex.real_smul,
    Complex.normSq_mul, Complex.normSq_ofReal]
  nlinarith [mul_nonneg (sub_nonneg.mpr hb2) hn]

theorem ball_preconnected : PreconnectedSpace Adelic.BallNatural.Ball := by
  exact isPreconnected_iff_preconnectedSpace.mp
    (ballDomain_starConvex.isPathConnected (show (0 : Fin 2 → ℂ) ∈ Adelic.BallGeometryData.ballDomain by norm_num [Adelic.BallGeometryData.ballDomain])).isConnected.isPreconnected

theorem holomorphic_continuous {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : Adelic.BallNatural.Ball → V) (hf : Adelic.BallGeometryData.BallHolomorphic f) : Continuous f := by
  have hc := hf.continuousOn.domRestrict
  apply hc.congr
  intro z
  change (if hz : Complex.normSq (z.val 0) + Complex.normSq (z.val 1) < 1 then
    f ⟨z.val,hz⟩ else 0) = f z
  exact dite_eq_left z.property

theorem constant_of_square (f : Adelic.BallNatural.Ball → ℂ) (hf : Continuous f)
    (hsq : ∀ z, f z ^ 2 = f origin ^ 2) (hne : f origin ≠ 0) :
    ∀ z, f z = f origin := by
  let : PreconnectedSpace Adelic.BallNatural.Ball := ball_preconnected
  have he : Set.EqOn f (fun _ => f origin) Set.univ :=
    isPreconnected_univ.eq_of_sq_eq hf.continuousOn continuousOn_const
      (fun z _ => hsq z) (fun _ => hne) (Set.mem_univ origin) rfl
  exact fun z => he (Set.mem_univ z)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic
