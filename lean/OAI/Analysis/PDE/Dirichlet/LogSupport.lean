import OAI.LinearAlgebra.Moore.Concavity

open Set
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- The supporting-hyperplane inequality for the actual Moore log determinant.
Both matrices belong to the genuine positive cone; no global extension of the
nonlinear operator is assumed. -/
theorem log_mooreDet_support {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hB : (OAI.LinearAlgebra.Moore.complexify B).PosDef) :
    Real.log (OAI.LinearAlgebra.Moore.mooreDet n B) - Real.log (OAI.LinearAlgebra.Moore.mooreDet n A) ≤
      OAI.LinearAlgebra.Moore.mooreDifferential n A (B - A) / OAI.LinearAlgebra.Moore.mooreDet n A := by
  have hD : (B - A).IsHermitian :=
    (OAI.LinearAlgebra.Moore.isHermitian_of_complexify hB.isHermitian).sub
      (OAI.LinearAlgebra.Moore.isHermitian_of_complexify hA.isHermitian)
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (OAI.LinearAlgebra.Moore.complexify (A + t • (B - A))).PosDef := by
    have hh := OAI.LinearAlgebra.Moore.convex_complexify_posDef n hA hB (sub_nonneg.mpr ht.2) ht.1
      (show (1 - t) + t = 1 by ring)
    have he : (1 - t) • A + t • B = A + t • (B - A) := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    rwa [he] at hh
  have hc := OAI.LinearAlgebra.Moore.concaveOn_log_mooreDet_affine A (B - A) 0 1 hD hpos
  have hentry (i j : Fin n) :
      HasDerivAt (fun t : ℝ ↦ (A + t • (B - A)) i j) ((B - A) i j) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (A i j)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const ((B - A) i j)) using 1
    simp
  have hder : HasDerivAt (fun t : ℝ ↦ OAI.LinearAlgebra.Moore.mooreDet n (A + t • (B - A)))
      (OAI.LinearAlgebra.Moore.mooreDifferential n A (B - A)) 0 := by
    simpa only [zero_smul, add_zero] using
      OAI.LinearAlgebra.Moore.hasDerivAt_mooreDet_path n (fun t : ℝ ↦ A + t • (B - A)) (B - A) 0 hentry
  have hlog := hder.log (by
    simpa only [zero_smul, add_zero] using (OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef A hA).ne')
  have hs := hc.slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Icc 0 1 by simp) zero_lt_one hlog
  have hab : A + (B - A) = B := by abel
  simpa [slope, hab] using hs

end OAI.Analysis.PDE.Dirichlet
