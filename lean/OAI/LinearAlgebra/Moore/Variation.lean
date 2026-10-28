import OAI.LinearAlgebra.Moore.Schur

/-! Cofactor restriction at singular spatial endpoints and exact path integrals. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix Set Filter
open scoped MatrixOrder ComplexOrder Topology

theorem continuous_hermitianBlock {n : ℕ} (ell : ℝ) (c : Fin n → Quaternion ℝ) :
    Continuous (fun D : Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦ hermitianBlock ell c D) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun j ↦ ?_) j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_apply j).comp (continuous_apply i)

/-- Restriction to the spatial block remains valid at a singular PSD endpoint.
No positivity is required of the full normal/spatial matrix. -/
theorem mooreCofactor_hermitianBlock_normal_posSemidef {n : ℕ}
    (ell : ℝ) (c : Fin n → Quaternion ℝ)
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hD : (complexify D).PosSemidef) :
    (mooreCofactor (n + 1) (hermitianBlock ell c D) 0 0).re = mooreDet n D := by
  let f : ℝ → ℝ := fun t ↦
    mooreDet (n + 1) (hermitianBlock ell c (D + t • 1) + coordinateProjector (n + 1) 0) -
      mooreDet (n + 1) (hermitianBlock ell c (D + t • 1)) - mooreDet n (D + t • 1)
  have hp : Continuous (fun t : ℝ ↦ D + t • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ))) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hb := (continuous_hermitianBlock ell c).comp hp
  have hf : Continuous f :=
    (((continuous_mooreDet (n + 1)).comp (hb.add continuous_const)).sub
      ((continuous_mooreDet (n + 1)).comp hb)).sub ((continuous_mooreDet n).comp hp)
  have ht : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h := mooreCofactor_hermitianBlock_normal ell c (D + t • 1)
      (complexify_add_pos_identity D hD ht)
    rw [mooreCofactor_diag] at h
    exact sub_eq_zero.mpr h
  have htzero : Tendsto f (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) (𝓝[>] 0) (𝓝 0)).congr' (by
      filter_upwards [he] with t h
      exact h.symm)
  have hz : f 0 = 0 := tendsto_nhds_unique ht htzero
  rw [mooreCofactor_diag]
  simpa only [f, zero_smul, add_zero, sub_eq_zero] using hz

/-- The cofactor differential integrates exactly to the determinant change. -/
theorem integral_mooreDifferential_affine {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (a b : ℝ) :
    (∫ t in a..b, mooreDifferential n (A + t • D) D) =
      mooreDet n (A + b • D) - mooreDet n (A + a • D) := by
  have hp : Continuous (fun t : ℝ ↦ (A + t • D, D)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const
  have hc := (continuous_mooreDifferential n).comp hp
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_mooreDet_affine A D t) (hc.intervalIntegrable a b)

theorem integral_mooreCofactor_pairing {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hD : D.IsHermitian) (a b : ℝ) :
    (∫ t in a..b, realTrace (mooreCofactor n (A + t • D) * D)) =
      mooreDet n (A + b • D) - mooreDet n (A + a • D) := by
  simp_rw [mooreCofactor_pairing n _ D hD]
  exact integral_mooreDifferential_affine A D a b

theorem integral_mooreCofactor_segment {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hD : D.IsHermitian) :
    (∫ t in (0 : ℝ)..1, realTrace (mooreCofactor n (A + t • D) * D)) =
      mooreDet n (A + D) - mooreDet n A := by
  simpa using integral_mooreCofactor_pairing A D hD 0 1

end OAI.LinearAlgebra.Moore
