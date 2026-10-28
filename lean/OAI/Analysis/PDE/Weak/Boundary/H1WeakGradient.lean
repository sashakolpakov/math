import OAI.Analysis.PDE.Weak.Elliptic.H1
import OAI.Analysis.PDE.Variational.WeakGradient
import OAI.Analysis.PDE.Green.GreenReal

/-! The gradient component of the H¹ graph completion is the actual
distributional gradient of its value component. -/

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem H1Zero.weak_derivative {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {q : H1Pair m}
    (hq : q ∈ H1Zero Ω) (j : Fin (m + 1))
    (φ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    (∫ x, (q.2 x) j * φ x) = -(∫ x, q.1 x * fderiv ℝ φ x (Pi.single j 1)) := by
  let dφ := fun x => fderiv ℝ φ x (Pi.single j 1)
  have hdc : Continuous dφ := OAI.Analysis.PDE.Green.continuous_directional hφ _
  have hds : HasCompactSupport dφ := hs.fderiv_apply ℝ _
  have hd : MemLp dφ 2 volume := hdc.memLp_of_hasCompactSupport hds
  have hvc : Continuous (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) := OAI.Analysis.PDE.Variational.continuous_coordinateTestVector j hφ.continuous
  have hvs : HasCompactSupport (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) := by
    change HasCompactSupport ((fun t : ℝ => t • EuclideanSpace.single j (1 : ℝ)) ∘ φ)
    apply hs.comp_left
    simp
  have hv : MemLp (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) 2 volume := hvc.memLp_of_hasCompactSupport hvs
  let Dφ := hd.toLp dφ
  let Vφ := hv.toLp (OAI.Analysis.PDE.Variational.coordinateTestVector j φ)
  have hleft (p : H1Pair m) : inner ℝ Vφ p.2 = ∫ x, φ x * (p.2 x) j := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with x hx
    change inner ℝ (hv.toLp (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) x) (p.2 x) = _
    rw [hx, OAI.Analysis.PDE.Variational.inner_coordinateTestVector]
  have hright (p : H1Pair m) : inner ℝ Dφ p.1 = ∫ x, dφ x * p.1 x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hd.coeFn_toLp] with x hx
    change inner ℝ (hd.toLp dφ x) (p.1 x) = _
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  have hc : IsClosed {p : H1Pair m | inner ℝ Vφ p.2 = -inner ℝ Dφ p.1} :=
    isClosed_eq (continuous_const.inner continuous_snd) (continuous_const.inner continuous_fst).neg
  have hmain : inner ℝ Vφ q.2 = -inner ℝ Dφ q.1 := by
    apply closure_minimal (s := smoothH1Graph Ω) _ hc hq
    rintro p ⟨u, hu, hus, _, rfl⟩
    change inner ℝ Vφ (smoothH1Pair u hu hus).2 = -inner ℝ Dφ (smoothH1Pair u hu hus).1
    rw [hleft, hright]
    have hgu : (smoothH1Pair u hu hus).2 =ᵐ[volume] OAI.Analysis.PDE.Variational.cellGradient u :=
      ((OAI.Analysis.PDE.Variational.continuous_cellGradient (hu.of_le (by simp))).memLp_of_hasCompactSupport
        (hasCompactSupport_cellGradient hus)).coeFn_toLp
    have hvu : (smoothH1Pair u hu hus).1 =ᵐ[volume] u :=
      (hu.continuous.memLp_of_hasCompactSupport hus).coeFn_toLp
    have hli : (∫ x, φ x * ((smoothH1Pair u hu hus).2 x) j) =
        ∫ x, φ x * fderiv ℝ u x (Pi.single j 1) := by
      apply integral_congr_ae
      filter_upwards [hgu] with x hx
      rw [hx]
      rfl
    have hri : (∫ x, dφ x * (smoothH1Pair u hu hus).1 x) = ∫ x, dφ x * u x := by
      apply integral_congr_ae
      filter_upwards [hvu] with x hx
      rw [hx]
    rw [hli, hri]
    exact OAI.Analysis.PDE.Green.integral_directional_by_parts hφ (hu.of_le (by simp)) hs (Pi.single j 1)
  rw [hleft, hright] at hmain
  simpa only [dφ, mul_comm] using hmain

end OAI.Analysis.PDE.Weak
