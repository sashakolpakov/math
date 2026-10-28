import OAI.Analysis.PDE.Green.FiberCoordinates

/-! Moving-fiber integration of the determinant energy. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

theorem integral_sublevel_fibers {n s : ℕ} {r f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    (hr : Continuous r) (hf : IntegrableOn f {x | r x < 0}) :
    (∫ x in {x | r x < 0}, f x) =
      ∫ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s, ∫ y in {y | r (fiberEmbedding n s z y) < 0},
        f (fiberEmbedding n s z y) := by
  have hS : MeasurableSet {x | r x < 0} := (isOpen_lt hr continuous_const).measurableSet
  rw [← integral_indicator hS,
    integral_fiberEmbedding ((integrable_indicator_iff hS).2 hf)]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : Continuous (fun y => fiberEmbedding n s z y) :=
    (continuous_fiberEmbedding n s).comp (continuous_const.prodMk continuous_id)
  have hSz : MeasurableSet {y | r (fiberEmbedding n s z y) < 0} :=
    (isOpen_lt (hr.comp hz) continuous_const).measurableSet
  rw [← integral_indicator hSz]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Set.indicator, Set.mem_ofPred_eq]

theorem integral_sublevel_time_weight {n s : ℕ} {r f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    (hr : Continuous r) (ρ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ)
    (hf : IntegrableOn (fun x => ρ (timeProjection n s x) * f x) {x | r x < 0}) :
    (∫ x in {x | r x < 0}, ρ (timeProjection n s x) * f x) =
      ∫ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s, ρ z *
        ∫ y in {y | r (fiberEmbedding n s z y) < 0}, f (fiberEmbedding n s z y) := by
  rw [integral_sublevel_fibers hr hf]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [timeProjection_fiberEmbedding]
  rw [integral_const_mul]

theorem continuous_spatialPencilEnergyDensity {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u) :
    Continuous (spatialPencilEnergyDensity e B u) := by
  have hBH := OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hB
  have huH := OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hu
  have hmat : Continuous (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s × ℝ =>
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e B p.1 + p.2 • OAI.Analysis.PDE.Dirichlet.quaternionHessian e u p.1) :=
    (hBH.comp continuous_fst).add (continuous_snd.smul (huH.comp continuous_fst))
  have hsub : Continuous (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s × ℝ =>
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B p.1 + p.2 • OAI.Analysis.PDE.Dirichlet.quaternionHessian e u p.1).submatrix
        Fin.succ Fin.succ) := by
    exact continuous_pi (fun i => continuous_pi (fun j =>
      (continuous_apply j.succ).comp ((continuous_apply i.succ).comp hmat)))
  have hdet : Continuous (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s × ℝ =>
      OAI.LinearAlgebra.Moore.mooreDet n ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e B p.1 + p.2 • OAI.Analysis.PDE.Dirichlet.quaternionHessian e u p.1).submatrix
        Fin.succ Fin.succ)) := by
    simpa only using! (OAI.LinearAlgebra.Moore.continuous_mooreDet n).comp hsub
  have hp : Continuous (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s × ℝ =>
      OAI.LinearAlgebra.Moore.mooreDet n ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + p.2 * u y) p.1).submatrix
        Fin.succ Fin.succ)) := by
    simpa only [quaternionHessian_add_mul e (hB.of_le (by norm_num))
      (hu.of_le (by norm_num))] using hdet
  exact hu.continuous.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hp 0 1)

def fiberDeterminantEnergy {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (r B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) : ℝ :=
  ∫ y in {y | r (fiberEmbedding n s z y) < 0},
    spatialPencilEnergyDensity e B u (fiberEmbedding n s z y)

def fiberDeterminantDifference {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (r B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) : ℝ :=
  ∫ y in {y | r (fiberEmbedding n s z y) < 0},
    OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun x => B x + u x) (fiberEmbedding n s z y)) -
      OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B (fiberEmbedding n s z y))

theorem continuous_time_laplacian {s : ℕ} (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ} (hη : ContDiff ℝ 3 η) :
    Continuous (Laplacian.laplacian η) := by
  have hc := OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hη
  refine (Quaternion.continuous_re.comp
    ((continuous_apply 0).comp ((continuous_apply 0).comp hc))).congr ?_
  intro z
  have ht := OAI.Analysis.PDE.Dirichlet.quaternionHessian_trace e he (hη.of_le (by norm_num)).contDiffAt (x := z)
  simpa only [Function.comp_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_one, Quaternion.re_coe] using!
    congrArg (fun q : Quaternion ℝ => q.re) ht

/-- The actual moving-fiber energy satisfies the weak extended-time Laplacian
identity. No differential or integration-by-parts identity is assumed. -/
theorem fiberDeterminantEnergy_weak_laplacian {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    {r u B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ}
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B)
    (hη : ContDiff ℝ 3 η) (hb : Bornology.IsBounded {x | r x < 0})
    (hrne : ∀ x ∈ closure {x | r x < 0}, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ y, r y = 0 → u y = 0)
    (hcommon : ∀ x, r x = 0 → ∃ w : Fin (n + 1) → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0)
    (hspatial : ∀ x, r x < 0 → ∀ t ∈ Icc (0 : ℝ) 1,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x).submatrix
        Fin.succ Fin.succ)).PosSemidef) :
    (∫ z, Laplacian.laplacian η z * fiberDeterminantEnergy e r B u z) =
      ∫ z, η z * fiberDeterminantDifference e r B u z := by
  have hden := continuous_spatialPencilEnergyDensity e hB hu
  have hΔ := continuous_time_laplacian e he hη
  have hd1 : Continuous (fun x => OAI.LinearAlgebra.Moore.mooreDet (n + 1)
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)) := by
    simpa only using! (OAI.LinearAlgebra.Moore.continuous_mooreDet (n + 1)).comp
      (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e (hB.add hu))
  have hd0 : Continuous (fun x => OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) := by
    simpa only using! (OAI.LinearAlgebra.Moore.continuous_mooreDet (n + 1)).comp
      (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hB)
  have hi1 := OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb
    ((hΔ.comp (timeProjection n s).continuous).mul hden)
  have hi2 : IntegrableOn (fun x => η (timeProjection n s x) *
      (OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) -
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x))) {x | r x < 0} :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb
    ((hη.continuous.comp (timeProjection n s).continuous).mul (hd1.sub hd0))
  unfold fiberDeterminantEnergy fiberDeterminantDifference
  rw [← integral_sublevel_time_weight hr.continuous _ hi1,
    ← integral_sublevel_time_weight hr.continuous _ hi2]
  exact determinant_energy_weak_time_laplacian e he hr hu hB hη hb hrne huz hcommon hspatial

end OAI.Analysis.PDE.Green
