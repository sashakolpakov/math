import OAI.Analysis.PDE.Schauder.Calculus.Schauder.FarField

/-! Radial second moments and the symmetry behind Newtonian kernel cancellation. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped BigOperators
namespace OAI.Analysis.PDE.Schauder

def radialMoment {m : ℕ} (ρ : ℝ → ℝ) (i j : Fin m) : ℝ :=
  ∫ y : EuclideanSpace ℝ (Fin m), ρ ‖y‖ * y i * y j

theorem radialMoment_offDiagonal {m : ℕ} (ρ : ℝ → ℝ) (i j : Fin m) (hij : i ≠ j) :
    radialMoment ρ i j = 0 := by
  let e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
    LinearIsometryEquiv.piLpCongrRight 2 fun k =>
      if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ
  have hei (y : EuclideanSpace ℝ (Fin m)) : e y i = -y i := by simp [e]
  have hej (y : EuclideanSpace ℝ (Fin m)) : e y j = y j := by simp [e, hij.symm]
  have he := MeasureTheory.integral_comp e
    (fun y : EuclideanSpace ℝ (Fin m) => ρ ‖y‖ * y i * y j)
  simp only [e.norm_map, hei, hej] at he
  have hf : (fun y : EuclideanSpace ℝ (Fin m) => ρ ‖y‖ * -y i * y j) =
      fun y => -(ρ ‖y‖ * y i * y j) := by funext y; ring
  rw [hf, integral_neg] at he
  dsimp [radialMoment]
  linarith

theorem radialMoment_diagonal_eq {m : ℕ} (ρ : ℝ → ℝ) (i j : Fin m) :
    radialMoment ρ i i = radialMoment ρ j j := by
  let e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have hei (y : EuclideanSpace ℝ (Fin m)) : e y i = y j := by
    simp [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  have he := MeasureTheory.integral_comp e
    (fun y : EuclideanSpace ℝ (Fin m) => ρ ‖y‖ * y i * y i)
  simp only [e.norm_map, hei] at he
  exact he.symm

theorem radialMoment_trace {m : ℕ} (ρ : ℝ → ℝ)
    (hint : ∀ i : Fin m, Integrable (fun y : EuclideanSpace ℝ (Fin m) => ρ ‖y‖ * y i * y i))
    (i : Fin m) :
    (m : ℝ) * radialMoment ρ i i =
      ∫ y : EuclideanSpace ℝ (Fin m), ρ ‖y‖ * ‖y‖ ^ 2 := by
  calc
    (m : ℝ) * radialMoment ρ i i = ∑ j : Fin m, radialMoment ρ j j := by
      simp_rw [radialMoment_diagonal_eq ρ _ i]
      simp
    _ = ∫ y : EuclideanSpace ℝ (Fin m), ∑ j : Fin m, ρ ‖y‖ * y j * y j := by
      exact (MeasureTheory.integral_finsetSum Finset.univ fun j _ => hint j).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [EuclideanSpace.real_norm_sq_eq]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring

end OAI.Analysis.PDE.Schauder
