import OAI.Analysis.PDE.Weak.Elliptic.Classical.Gradient
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

def classicalDivergence (H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) : ℝ :=
  ∑ i : Fin (m + 1), fderiv ℝ (fun y ↦ H y i) x (Pi.single i 1)

theorem continuous_classicalDivergence {H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m}
    (hH : ContDiff ℝ 1 H) : Continuous (classicalDivergence H) := by
  apply continuous_finsetSum
  intro i _
  exact OAI.Analysis.PDE.Green.continuous_directional
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hH) _

theorem classicalDivergence_weak_equation {H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m}
    (hH : ContDiff ℝ 1 H) (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) :
    WeakDivergenceEquation Ω H (fun x ↦ -classicalDivergence H x) := by
  intro φ hφ hs hsub
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hHi (i : Fin (m + 1)) : ContDiff ℝ 1 (fun y ↦ H y i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hH
  have hi (i : Fin (m + 1)) :
      Integrable (fun x ↦ H x i * fderiv ℝ φ x (Pi.single i 1)) :=
    ((hHi i).continuous.mul (OAI.Analysis.PDE.Green.continuous_directional hφ1 _)).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ _).mul_left
  have hdi (i : Fin (m + 1)) :
      Integrable (fun x ↦ fderiv ℝ (fun y ↦ H y i) x (Pi.single i 1) * φ x) :=
    ((OAI.Analysis.PDE.Green.continuous_directional (hHi i) _).mul hφ.continuous).integrable_of_hasCompactSupport
      hs.mul_left
  have hinner (x : OAI.Analysis.PDE.Variational.CellCoordinates m) : inner ℝ (H x) (OAI.Analysis.PDE.Variational.cellGradient φ x) =
      ∑ i, H x i * fderiv ℝ φ x (Pi.single i 1) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, OAI.Analysis.PDE.Variational.cellGradient_apply]
    congr 1
    funext i
    ring
  simp_rw [hinner]
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  have he : (∑ i, ∫ x, H x i * fderiv ℝ φ x (Pi.single i 1)) =
      -∑ i, ∫ x, fderiv ℝ (fun y ↦ H y i) x (Pi.single i 1) * φ x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hh := OAI.Analysis.PDE.Green.integral_directional_by_parts (μ := volume) hφ1 (hHi i) hs (Pi.single i 1)
    have hh' : (∫ x, fderiv ℝ (fun y ↦ H y i) x (Pi.single i 1) * φ x) =
        -(∫ x, H x i * fderiv ℝ φ x (Pi.single i 1)) := by
      simpa only [mul_comm] using hh
    linarith
  rw [he]
  simp_rw [classicalDivergence, neg_mul, Finset.sum_mul]
  rw [integral_neg, integral_finsetSum _ (fun i _ ↦ hdi i)]

/-- A C¹ flux and continuous forcing satisfying the weak equation satisfy
the classical divergence equation at every interior point. -/
theorem WeakDivergenceEquation.classical_eq
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    {H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m} (hH : ContDiff ℝ 1 H)
    {f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hf : Continuous f)
    (he : WeakDivergenceEquation Ω H f) :
    ∀ x ∈ Ω, -classicalDivergence H x = f x := by
  have hd := continuous_classicalDivergence hH
  have hlocal : LocallyIntegrableOn (fun x ↦ -classicalDivergence H x - f x) Ω volume :=
    (hd.neg.sub hf).locallyIntegrable.locallyIntegrableOn Ω
  have hz : ∀ᵐ x ∂volume, x ∈ Ω → -classicalDivergence H x - f x = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
    intro φ hφ hs hsub
    have hi : Integrable (fun x ↦ φ x * -classicalDivergence H x) :=
      (hφ.continuous.mul hd.neg).integrable_of_hasCompactSupport hs.mul_right
    have hj : Integrable (fun x ↦ φ x * f x) :=
      (hφ.continuous.mul hf).integrable_of_hasCompactSupport hs.mul_right
    have heq := classicalDivergence_weak_equation hH Ω φ hφ hs hsub
    rw [he φ hφ hs hsub] at heq
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub hi hj]
    have heq' : (∫ x, φ x * -classicalDivergence H x) = ∫ x, φ x * f x := by
      simpa only [mul_comm] using heq.symm
    exact sub_eq_zero.mpr heq'
  have hae : (fun x ↦ -classicalDivergence H x) =ᵐ[volume.restrict Ω] f := by
    change ∀ᵐ x ∂volume.restrict Ω, -classicalDivergence H x = f x
    rw [ae_restrict_iff' hΩ.measurableSet]
    filter_upwards [hz] with x hx
    exact fun hy ↦ sub_eq_zero.mp (hx hy)
  exact Measure.eqOn_open_of_ae_eq (μ := volume) hae hΩ hd.neg.continuousOn hf.continuousOn

end OAI.Analysis.PDE.Weak
