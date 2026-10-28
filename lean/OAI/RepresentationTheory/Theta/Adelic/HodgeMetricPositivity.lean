import OAI.RepresentationTheory.Theta.Adelic.BallFramePositivity
import OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates

/-! # Hodge Metric Positivity -/

namespace OAI.RepresentationTheory.Theta.Adelic.HodgeMetricPositivity

noncomputable section

/-! The actual Hodge frame has positive Hermitian energy at every
real place and on every multiplicity line. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.BallFramePositivity OAI.RepresentationTheory.Theta.Adelic.BallFramePositivity.RankThreeHodgeAction OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def geometricEnergy (w : BallGeometryData.ComplexPhase A) : ℝ :=
  ∑ v, ∑ ij, (ComplexPhaseCoordinates.tensorDualSign A (v, ij)).re *
    (Complex.normSq ((w v).1 ij) - Complex.normSq ((w v).2 ij))

def localFrameEnergy (z : BallNatural.Ball) (v : Fin A.places) (a : Fin 3 → ℂ) : ℝ :=
  if v = A.distinguished then BallFramePositivity.ballFrameEnergy z a else ∑ i, Complex.normSq (a i)

theorem localFrameEnergy_nonneg (z : BallNatural.Ball) (v : Fin A.places) (a : Fin 3 → ℂ) :
    0 ≤ localFrameEnergy A z v a := by
  by_cases hv : v = A.distinguished
  · rw [localFrameEnergy, ite_eq_left hv]
    exact BallFramePositivity.ballFrameEnergy_nonneg z a
  · rw [localFrameEnergy, ite_eq_right hv]
    exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (a i))

theorem localFrameEnergy_pos (z : BallNatural.Ball) (v : Fin A.places) (a : Fin 3 → ℂ) (ha : a ≠ 0) :
    0 < localFrameEnergy A z v a := by
  by_cases hv : v = A.distinguished
  · rw [localFrameEnergy, ite_eq_left hv]
    exact BallFramePositivity.ballFrameEnergy_pos z a ha
  · rw [localFrameEnergy, ite_eq_right hv]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (a j))
      ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

theorem distinguished_tensor_sign (i : Fin 3) (j : Fin m) :
    (ComplexPhaseCoordinates.tensorDualSign A (A.distinguished, i, j)).re = if i = 2 then (1 : ℝ) else -1 := by
  by_cases hi : i = 2 <;> simp [ComplexPhaseCoordinates.tensorDualSign, A.distinguished_sign, hi]

theorem geometricFrame_energy (z : BallNatural.Ball) (a : BallGeometryData.FrameIndex A → ℂ) :
    geometricEnergy A (BallGeometryData.geometricFrame A z a) =
      ∑ v, ∑ j : Fin m, localFrameEnergy A z v (fun i => a (v, i, j)) := by
  change (∑ v, ∑ ij, (ComplexPhaseCoordinates.tensorDualSign A (v, ij)).re *
    (Complex.normSq ((BallGeometryData.geometricFrame A z a v).1 ij) -
      Complex.normSq ((BallGeometryData.geometricFrame A z a v).2 ij))) = _
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hv : v = A.distinguished
  · subst v
    rw [localFrameEnergy, ite_eq_left rfl]
    calc
      _ = ∑ i : Fin 3, (if i = 2 then (1 : ℝ) else -1) *
          (Complex.normSq (BallFramePositivity.RankThreeHodgeAction.standardHodgeColumn z (fun k => a (A.distinguished, k, j)) i) -
           Complex.normSq (BallFramePositivity.RankThreeHodgeAction.dualHodgeColumn z (fun k => a (A.distinguished, k, j)) i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [distinguished_tensor_sign]
        simp [BallGeometryData.geometricFrame, BallFramePositivity.RankThreeHodgeAction.standardHodgeColumn, BallFramePositivity.RankThreeHodgeAction.dualHodgeColumn]
      _ = _ := BallFramePositivity.ballFrameEnergy_formula z _
  · by_cases hp : A.positive v j <;>
      simp [localFrameEnergy, BallGeometryData.geometricFrame, ComplexPhaseCoordinates.tensorDualSign, hv, hp]

theorem geometricFrame_energy_pos (z : BallNatural.Ball) (a : BallGeometryData.FrameIndex A → ℂ) (ha : a ≠ 0) :
    0 < geometricEnergy A (BallGeometryData.geometricFrame A z a) := by
  rw [geometricFrame_energy]
  obtain ⟨⟨v, i, j⟩, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  refine Finset.sum_pos'
    (fun v _ => Finset.sum_nonneg (fun j _ => localFrameEnergy_nonneg A z v _))
    ⟨v, Finset.mem_univ v, ?_⟩
  refine Finset.sum_pos' (fun j _ => localFrameEnergy_nonneg A z v _)
    ⟨j, Finset.mem_univ j, localFrameEnergy_pos A z v _ ?_⟩
  intro h
  exact hi (congrFun h i)

end

end OAI.RepresentationTheory.Theta.Adelic.HodgeMetricPositivity
