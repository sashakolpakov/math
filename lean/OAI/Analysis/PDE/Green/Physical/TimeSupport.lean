import OAI.Analysis.PDE.Green.Physical.TimeBox

/-! Compact time tests can be compared with the actual moving-fiber energy
without assigning an artificial boundary condition outside their support. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory OAI.Analysis.PDE.Dirichlet
open scoped Topology

theorem laplacian_nonzero_mem_tsupport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} (hx : Laplacian.laplacian f x ≠ 0) : x ∈ tsupport f := by
  by_contra hn
  have hz : f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hh := (InnerProductSpace.laplacian_congr_nhds hz).eq_of_nhds
  apply hx
  simpa only [InnerProductSpace.laplacian_const, Pi.zero_apply] using hh

theorem exists_time_test_box {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ} (hη : HasCompactSupport η) :
    ∃ L : ℝ, 0 < L ∧ ∀ z ∈ tsupport η, ∀ j : Fin 3, -L < z (0, j) ∧ z (0, j) < L := by
  obtain ⟨C, hC⟩ := hη.isBounded.exists_norm_le
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro z hz j
  have hh : ‖z (0, j)‖ ≤ C := (PiLp.norm_apply_le z (0, j)).trans (hC z hz)
  rw [Real.norm_eq_abs, abs_le] at hh
  constructor <;> linarith [le_abs_self C]

theorem physicalTimeBox_weak_energy_eq {d m k : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (b : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1)) (L a : ℝ) (ha : 0 < a)
    (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ)
    (ht : ∀ z ∈ tsupport η, a ≤ ‖energyComplexTime z‖ ∧ ‖energyComplexTime z‖ ≤ 4)
    (hz : ∀ z ∈ tsupport η, ∀ j : Fin 3, -L ≤ z (0, j) ∧ z (0, j) ≤ L)
    (R : (ℂ × (Option (Fin d) → ℂ)) → ℝ)
    (hneg : ∀ z ∈ tsupport η, ∀ q, R (energyComplexTime z, q) < 0 ↔
      OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (energyComplexTime z) q < 0)
    (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ))
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ) :
    (∫ z, Laplacian.laplacian η z * setFiberCombinedEnergy e lam
      ((euclideanCoordinates c ⁻¹' Icc (physicalTimeBoxLower c L) (physicalTimeBoxUpper c L)) ∩
        {x | R (fullPhysicalProjection d x) < 0}) A B u z) =
    ∫ z, Laplacian.laplacian η z * setFiberCombinedEnergy e lam (physicalEnergyCell d a) A B u z := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  by_cases hΔ : Laplacian.laplacian η z = 0
  · simp only [hΔ, zero_mul]
  · have hzs := laplacian_nonzero_mem_tsupport hΔ
    rw [physicalTimeBox_energy_eq c b L a ha z (ht z hzs).1 (ht z hzs).2 (hz z hzs)
      R (hneg z hzs) e lam A B u]

end OAI.Analysis.PDE.Green
