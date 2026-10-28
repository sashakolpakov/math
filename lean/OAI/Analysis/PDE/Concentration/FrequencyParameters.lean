import OAI.Analysis.PDE.Concentration.PeriodicPacket

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.Fourier.WavePackets

def realGaussianVelocity {d : ℕ} (η : OAI.Analysis.Calculus.Current.SpatialSpace d) (i : Fin d) : ℝ :=
  η (some i) / gaussianFrequencyK η

theorem packet_frequency_parameters {d : ℕ} (η : OAI.Analysis.Calculus.Current.SpatialSpace d)
    (hk : 0 < gaussianFrequencyK η) :
    packetSpatialFrequency (gaussianFrequencyK η) (realGaussianVelocity η) = η := by
  let k := gaussianFrequencyK η
  have hk0 : k ≠ 0 := hk.ne'
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hks : k * Real.sqrt 2 = η none + ‖η‖ := by
    dsimp [k, gaussianFrequencyK]
    exact div_mul_cancel₀ _ hs0
  have hnorm : ‖η‖ ^ 2 = η none ^ 2 + ∑ i : Fin d, η (some i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
    simp only [Real.norm_eq_abs, sq_abs]
  have hk2 : 2 * k ^ 2 = (η none + ‖η‖) ^ 2 := by
    calc
      _ = (k * Real.sqrt 2) ^ 2 := by rw [mul_pow, hs2]; ring
      _ = _ := by rw [hks]
  have hrel : (∑ i : Fin d, η (some i) ^ 2) =
      2 * k ^ 2 - 2 * Real.sqrt 2 * k * η none := by
    have he := congrArg (fun z : ℝ => 2 * z * η none) hks
    nlinarith [he]
  have hv : (∑ i, realGaussianVelocity η i * realGaussianVelocity η i) =
      (∑ i : Fin d, η (some i) ^ 2) / k ^ 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [realGaussianVelocity, k]
    ring
  ext i
  cases i with
  | none =>
    change k * (1 - (∑ i, realGaussianVelocity η i * realGaussianVelocity η i) / 2) /
      Real.sqrt 2 = η none
    rw [hv, hrel]
    field_simp
    ring
  | some i =>
    change k * (η (some i) / k) = η (some i)
    field_simp

def spatialFinIsometry (d : ℕ) : OAI.Analysis.Calculus.Current.SpatialSpace d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSuccEquiv d).symm

theorem spatialFinIsometry_apply {d : ℕ} (η : OAI.Analysis.Calculus.Current.SpatialSpace d) (i : Fin (d + 1)) :
    spatialFinIsometry d η i = η (finSuccEquiv d i) := by
  simp [spatialFinIsometry, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem spatialFinIsometry_symm_apply {d : ℕ} (η : EuclideanSpace ℝ (Fin (d + 1)))
    (i : Option (Fin d)) :
    (spatialFinIsometry d).symm η i = η ((finSuccEquiv d).symm i) := by
  simp [spatialFinIsometry, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- A standard torus frequency expressed in a rotated physical sector frame. -/
def orientedPeriodicFrequency {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (m : Fin (d + 1) → ℤ) : OAI.Analysis.Calculus.Current.SpatialSpace d :=
  R ((spatialFinIsometry d).symm (OAI.Analysis.Fourier.WavePackets.periodicFrequency m))

theorem orientedPeriodicFrequency_quantized {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (m : Fin (d + 1) → ℤ)
    (i : Option (Fin d)) :
    inner ℝ (orientedPeriodicFrequency R m) (R (EuclideanSpace.single i 1)) =
      (m ((finSuccEquiv d).symm i) : ℝ) * (2 * Real.pi) / 100 := by
  rw [orientedPeriodicFrequency, R.inner_map_map, EuclideanSpace.inner_single_right]
  simp only [starRingEnd_apply, star_trivial, one_mul, spatialFinIsometry_symm_apply]
  change (2 * Real.pi / 100) * (m ((finSuccEquiv d).symm i) : ℝ) = _
  ring

theorem norm_orientedPeriodicFrequency {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (m : Fin (d + 1) → ℤ) :
    ‖orientedPeriodicFrequency R m‖ = ‖OAI.Analysis.Fourier.WavePackets.periodicFrequency m‖ := by
  rw [orientedPeriodicFrequency, R.norm_map, (spatialFinIsometry d).symm.norm_map]

end OAI.Analysis.PDE.Concentration
