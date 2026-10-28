import OAI.LinearAlgebra.Moore.Rank.Mixed.Binomial
import OAI.LinearAlgebra.Moore.Rank.BernsteinIntegral

noncomputable section
namespace OAI.LinearAlgebra.Moore

/-- Exact integral of the Moore determinant along a matrix segment.
The normalized Bernstein coefficients all integrate to `1 / (m + 1)`.
This polynomial identity requires neither positivity nor a rank bound. -/
theorem integral_mooreDet_segment_mixed (m : ℕ)
    (D B : Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    (∫ t in (0 : ℝ)..1, mooreDet m (t • D + (1-t) • B)) =
      (1 / ((m : ℝ)+1)) * ∑ j ∈ Finset.range (m+1),
        mixedMoore m (fun i : Fin m => if i.val < j then B else D) := by
  simp_rw [mooreDet_segment_mixed B D]
  rw [intervalIntegral.integral_finsetSum, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    have he : (fun t : ℝ => (m.choose j : ℝ) * t^(m-j) * (1-t)^j *
        mixedMoore m (fun i : Fin m => if i.val < j then B else D)) =
        (fun t : ℝ => ((m.choose j : ℝ) * (t^(m-j) * (1-t)^j)) *
          mixedMoore m (fun i : Fin m => if i.val < j then B else D)) := by
      funext t
      ring
    rw [he, intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      bernstein_integral m j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  · intro j hj
    simpa only [mul_assoc] using
      ((intervalIntegrable_bernstein m j).const_mul (m.choose j : ℝ)).mul_const
        (mixedMoore m (fun i : Fin m => if i.val < j then B else D))

end OAI.LinearAlgebra.Moore
