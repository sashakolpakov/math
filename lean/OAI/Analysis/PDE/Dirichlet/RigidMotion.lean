import OAI.Analysis.Calculus.Quaternion.Algebra

/-! The quaternionic infinitesimal rotation used in the mixed boundary
derivative estimate of `sections/dirichlet.tex`. -/

open scoped Matrix
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

abbrev Q := Quaternion ℝ

def quaternionPairing {ι : Type*} [Fintype ι] (x y : ι → Q) : Q :=
  ∑ i, star (x i) * y i

/-- Equation (dirichlet-rigid-motion), with the multiplication order retained. -/
def rigidMotionMatrix {ι : Type*} [Fintype ι] (ν v : ι → Q) : Matrix ι ι Q :=
  fun a b ↦ v a * star (ν b) - ν a * star (v b) -
    ν a * quaternionPairing ν v * star (ν b)

theorem star_quaternionPairing {ι : Type*} [Fintype ι] (x y : ι → Q) :
    star (quaternionPairing x y) = quaternionPairing y x := by
  simp [quaternionPairing, star_sum, star_mul]

theorem star_of_re_eq_zero (q : Q) (h : q.re = 0) : star q = -q := by
  ext <;> simp [h]

/-- Real orthogonality makes the infinitesimal matrix skew-Hermitian. -/
theorem rigidMotionMatrix_skew {ι : Type*} [Fintype ι] (ν v : ι → Q)
    (htangent : (quaternionPairing ν v).re = 0) :
    (rigidMotionMatrix ν v)ᴴ = -rigidMotionMatrix ν v := by
  have ha := star_of_re_eq_zero (quaternionPairing ν v) htangent
  apply Matrix.ext
  intro a b
  simp only [Matrix.conjTranspose_apply, rigidMotionMatrix, Matrix.neg_apply,
    star_sub, star_mul, star_star, ha]
  noncomm_ring

/-- Every real tangent vector is attained by an infinitesimal
quaternionic-unitary rotation of a unit normal. -/
theorem rigidMotionMatrix_normal {ι : Type*} [Fintype ι] (ν v : ι → Q)
    (hunit : quaternionPairing ν ν = 1)
    (htangent : (quaternionPairing ν v).re = 0) :
    rigidMotionMatrix ν v *ᵥ ν = v := by
  have ha := star_of_re_eq_zero (quaternionPairing ν v) htangent
  have hswap : quaternionPairing v ν = -quaternionPairing ν v := by
    rw [← star_quaternionPairing, ha]
  funext a
  simp only [Matrix.mulVec, dotProduct, rigidMotionMatrix, sub_mul,
    Finset.sum_sub_distrib, mul_assoc]
  simp only [← Finset.mul_sum]
  change v a * quaternionPairing ν ν -
    ν a * quaternionPairing v ν -
    ν a * (quaternionPairing ν v * quaternionPairing ν ν) = v a
  rw [hunit, hswap]
  noncomm_ring

end OAI.Analysis.PDE.Dirichlet
