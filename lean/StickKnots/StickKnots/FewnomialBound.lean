import StickKnots.Counting

/-!
# Conditional assembly of the fewnomial knot-count bound

The external topology and real-algebraic geometry enter this file only as
named hypotheses.  Everything after those hypotheses--including the crucial
factorial saving in the Barone--Basu sum--is proved in Lean.
-/

namespace StickKnots

open scoped BigOperators

/-- The weighted partial binomial sum appearing in the relevant
Barone--Basu component estimate. -/
def knotBBSum (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (affineSliceDim N + 1),
    (4 : ℝ) ^ j * (wallCount N + 1).choose j

theorem knotBBSum_le_entropy {N : ℕ} (hN : 5 ≤ N) :
    knotBBSum N ≤
      (affineSliceDim N + 1 : ℝ) *
        ((((12 * (wallCount N + 1) : ℕ) : ℝ) ^ affineSliceDim N) /
          (affineSliceDim N : ℝ) ^ affineSliceDim N) := by
  apply weighted_partial_choose_le
  · unfold affineSliceDim
    omega
  · exact knot_parameters_half_range hN

private theorem wall_plus_one_le_vertex_mul_dim {N : ℕ} (hN : 5 ≤ N) :
    wallCount N + 1 ≤ N * affineSliceDim N := by
  rcases hN.eq_or_lt with rfl | hNgt
  · decide
  · have h6N : 6 ≤ N := by omega
    have hc : N.choose 2 < N ^ 2 := Nat.choose_lt_pow (by omega) (by omega)
    have hc' : N.choose 2 + 1 ≤ N ^ 2 := by omega
    rw [wallCount_eq_choose_two (by omega)]
    calc
      N.choose 2 + 1 ≤ N ^ 2 := hc'
      _ = N * N := by ring
      _ ≤ N * affineSliceDim N := by
        apply Nat.mul_le_mul_left
        unfold affineSliceDim
        omega

/-- Knot-specialized form: because the number of walls is quadratic and the
slice dimension is linear, the entropy bound has base at most `12N`. -/
theorem knotBBSum_le_linear_base {N : ℕ} (hN : 5 ≤ N) :
    knotBBSum N ≤
      (affineSliceDim N + 1 : ℝ) * (12 * N : ℝ) ^ affineSliceDim N := by
  have hm : 0 < (affineSliceDim N : ℝ) := by
    have : 0 < affineSliceDim N := by unfold affineSliceDim; omega
    exact_mod_cast this
  have hratio :
      (((12 * (wallCount N + 1) : ℕ) : ℝ) / (affineSliceDim N : ℝ))
        ≤ (12 * N : ℝ) := by
    rw [div_le_iff₀ hm]
    have hnat := Nat.mul_le_mul_left 12 (wall_plus_one_le_vertex_mul_dim hN)
    have hreal :
        (((12 * (wallCount N + 1) : ℕ) : ℝ)) ≤
          ((12 * (N * affineSliceDim N) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa [mul_assoc] using hreal
  calc
    knotBBSum N ≤
        (affineSliceDim N + 1 : ℝ) *
          ((((12 * (wallCount N + 1) : ℕ) : ℝ) ^ affineSliceDim N) /
            (affineSliceDim N : ℝ) ^ affineSliceDim N) := knotBBSum_le_entropy hN
    _ = (affineSliceDim N + 1 : ℝ) *
          ((((12 * (wallCount N + 1) : ℕ) : ℝ) /
            (affineSliceDim N : ℝ)) ^ affineSliceDim N) := by rw [div_pow]
    _ ≤ (affineSliceDim N + 1 : ℝ) * (12 * N : ℝ) ^ affineSliceDim N := by
      gcongr

/-- Conditional upper arithmetic wrapper after explicitly named external inputs.

* `ambientIsotopy_affineSlice` is the topology/normalization statement that
  every chamber is reached by one of the two oriented affine slices.
* `baroneBasu_plus` and `baroneBasu_minus` are the component estimates on
  those slices; `bbFactor^m` records the fixed-degree factor.

No axiom is declared: a caller must supply proofs of these inputs. -/
theorem chamber_count_le_from_external_inputs
    {N chamberCount plusComponents minusComponents bbFactor : ℕ}
    (hN : 5 ≤ N)
    (ambientIsotopy_affineSlice :
      chamberCount ≤ plusComponents + minusComponents)
    (baroneBasu_plus :
      (plusComponents : ℝ) ≤ (bbFactor : ℝ) ^ affineSliceDim N * knotBBSum N)
    (baroneBasu_minus :
      (minusComponents : ℝ) ≤ (bbFactor : ℝ) ^ affineSliceDim N * knotBBSum N) :
    (chamberCount : ℝ) ≤
      2 * (bbFactor : ℝ) ^ affineSliceDim N *
        (affineSliceDim N + 1 : ℝ) * (12 * N : ℝ) ^ affineSliceDim N := by
  have htop : (chamberCount : ℝ) ≤ plusComponents + minusComponents := by
    exact_mod_cast ambientIsotopy_affineSlice
  have htwo : (chamberCount : ℝ) ≤
      2 * ((bbFactor : ℝ) ^ affineSliceDim N * knotBBSum N) := by
    linarith
  calc
    (chamberCount : ℝ) ≤
        2 * ((bbFactor : ℝ) ^ affineSliceDim N * knotBBSum N) := htwo
    _ ≤ 2 * ((bbFactor : ℝ) ^ affineSliceDim N *
          ((affineSliceDim N + 1 : ℝ) *
            (12 * N : ℝ) ^ affineSliceDim N)) := by
      gcongr
      exact knotBBSum_le_linear_base hN
    _ = 2 * (bbFactor : ℝ) ^ affineSliceDim N *
          (affineSliceDim N + 1 : ℝ) * (12 * N : ℝ) ^ affineSliceDim N := by ring

/-- Baseline lower-bound arithmetic.  The cited Malyutin--Stupakov enumeration
and the applicability of the Huh--Oh stick/arc conversion are represented by
the single named transfer hypothesis.  Separately, `arcIndexBudget_fits`
checks the numerical cutoff used by that external transfer; this wrapper uses
the Lean-checked factorial-to-power estimate. -/
theorem stick_knot_count_lower_from_external_inputs
    {N stickKnotCount : ℕ} (hN : 9 ≤ N)
    (malyutinStupakov_huhOh_transfer :
      (factorialRank N).factorial ≤ 2 * stickKnotCount) :
    ((factorialRank N : ℝ) / 3) ^ factorialRank N / 2 ≤ (stickKnotCount : ℝ) := by
  have hfac : (((factorialRank N).factorial : ℕ) : ℝ) ≤ 2 * stickKnotCount := by
    exact_mod_cast malyutinStupakov_huhOh_transfer
  have hpow := factorialRank_factorial_lower hN
  linarith

end StickKnots
