import OAI.Analysis.PDE.Weak.Boundary.Halfspace.Smooth
import OAI.Analysis.PDE.Weak.Elliptic.SmoothExtension
import OAI.Analysis.PDE.Weak.Elliptic.SmoothRegularity

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Actual finite-order boundary regularity with only local ellipticity
and smooth local data. No coefficient derivative estimates are inputs. -/
theorem halfspace_local_smooth_regular_near_point
    (k : Fin (m + 1)) (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam : ℝ} (hlam : 0 < lam)
    (N : ℕ) {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    (hell : ∀ x ∈ U, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero {x | 0 < x k})
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ x ∂volume, x ∈ {x | 0 < x k} ∩ U → f x = g x)
    (he : WeakDivergenceEquation ({x | 0 < x k} ∩ U) (fun x => A x (p.2 x)) f)
    {x₀ : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx₀ : x₀ ∈ U) :
    ∃ V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      WeakRegularity ({x | 0 < x k} ∩ V) (N + 1) p.2 ∧
      WeakRegularity ({x | 0 < x k} ∩ V) (N + 2) p.1 := by
  obtain ⟨θ, U₀, hU₀, hxU₀, hU₀U, hθ, hθs, hθsub, hθrange, hθone⟩ :=
    exists_cutoff_with_open_plateau hU hx₀
  let B := ellipticExtension A θ lam
  have hB : ContDiff ℝ ∞ B := (ellipticExtension_smoothBounded hA hθ hθs lam).1
  have hBe : ∀ y z, lam * ‖z‖ ^ 2 ≤ inner ℝ (B y z) z :=
    ellipticExtension_elliptic hθrange hθsub hell
  have hfixed : ∀ y ∉ tsupport θ, B y = lam • ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Variational.CellVectors m) := by
    intro y hy
    simp [B, ellipticExtension, image_eq_zero_of_notMem_tsupport hy]
  let gθ := fun y => θ y * g y
  have hgθ : ContDiff ℝ ∞ gθ := hθ.mul hg
  have hsθ : HasCompactSupport gθ := hθs.mul_right
  let fθ : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) :=
    (hgθ.continuous.memLp_of_hasCompactSupport hsθ).toLp gθ
  have hfθ : WeakRegularity ({x | 0 < x k} ∩ U₀) N fθ :=
    weakRegularity_of_smooth_compact hgθ hsθ _ N
  have heB : WeakDivergenceEquation ({x | 0 < x k} ∩ U₀) (fun y => B y (p.2 y)) fθ := by
    apply OAI.Analysis.PDE.Variational.weakEquation_congr_on he (inter_subset_inter_right _ hU₀U)
    · apply Eventually.of_forall
      intro y hy
      rw [show B y = A y from ellipticExtension_eq lam (hθone y hy.2)]
    · filter_upwards [hfg, (hgθ.continuous.memLp_of_hasCompactSupport hsθ).coeFn_toLp] with y hy hz
      intro hyU
      rw [hz, hy ⟨hyU.1, hU₀U hyU.2⟩]
      change θ y * g y = g y
      rw [hθone y hyU.2, one_mul]
  obtain ⟨V, hV, hxV, hVU₀, hr, hv⟩ := halfspace_smooth_regular_near_point k B hB hθs
    (lam • ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Variational.CellVectors m)) hfixed hlam hBe N hU₀ p hp fθ hfθ heB hxU₀
  exact ⟨V, hV, hxV, hVU₀.trans hU₀U, hr, hv⟩

end OAI.Analysis.PDE.Weak
