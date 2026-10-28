import OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilies
import OAI.RepresentationTheory.Theta.Geometric.Finite.AutomorphyTrace

/-! # Consecutive Gauge -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta

noncomputable section

/-! Quotients of coordinates in consecutive theta powers have exactly the
original automorphy factor. Their frame ratios are the corresponding
products of projective hyperplane transition ratios. -/

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
  (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hdeg : G.degree = F.degree + 1)

def consecutiveGauge (i : Fin (F.projectiveDimension + 1)) (j : Fin (G.projectiveDimension + 1))
    (z : Φ.space) : ℂ := G.coordinate j z / F.coordinate i z

include hdeg

theorem consecutiveGauge_translates (i : Fin (F.projectiveDimension + 1))
    (j : Fin (G.projectiveDimension + 1)) (l : Φ.periodIntegerLattice) (z : Φ.space) :
    consecutiveGauge F G i j (z + l.val) = J.value l z * consecutiveGauge F G i j z := by
  unfold consecutiveGauge
  have hpower : J.value l z ^ G.degree = J.value l z ^ (F.degree + 1) :=
    congrArg (fun n : ℕ => J.value l z ^ n) hdeg
  rw [(G.coordinate j).translates, (F.coordinate i).translates, hpower, pow_succ]
  field_simp [J.value_ne_zero l z]

omit hdeg in
theorem consecutiveGauge_ne_zero (i : Fin (F.projectiveDimension + 1))
    (j : Fin (G.projectiveDimension + 1)) (z : Φ.space)
    (hi : F.coordinate i z ≠ 0) (hj : G.coordinate j z ≠ 0) :
    consecutiveGauge F G i j z ≠ 0 := div_ne_zero hj hi

omit hdeg in
theorem consecutiveGauge_differentiableAt (i : Fin (F.projectiveDimension + 1))
    (j : Fin (G.projectiveDimension + 1)) (z : Φ.space) (hi : F.coordinate i z ≠ 0) :
    DifferentiableAt ℂ (consecutiveGauge F G i j) z :=
  ((G.coordinate j).regular.contDiffAt.div (F.coordinate i).regular.contDiffAt hi).differentiableAt
    (by norm_num)

omit hdeg in
theorem consecutiveGauge_ratio (i k : Fin (F.projectiveDimension + 1))
    (j l : Fin (G.projectiveDimension + 1)) (z : Φ.space) :
    consecutiveGauge F G k l z / consecutiveGauge F G i j z =
      (G.coordinate l z / G.coordinate j z) / (F.coordinate k z / F.coordinate i z) := by
  unfold consecutiveGauge
  simp only [div_div_div_comm]

end

end OAI.RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta
