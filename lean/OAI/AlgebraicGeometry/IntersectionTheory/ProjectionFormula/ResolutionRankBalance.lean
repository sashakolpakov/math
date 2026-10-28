import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.RankEuler

/-! # Resolution Rank Balance -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionRankBalance

noncomputable section

/-! A length-two free resolution of a torsion module has the rank
balance needed for its two square determinant matrices. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] [IsDomain R]
  (M : ModuleCat.{u} R) [Module.Finite R M] (P : ProjectiveResolution M)

theorem rank_eq
    (hP : ∀ n, Module.Finite R (P.complex.X n) ∧ Module.Free R (P.complex.X n))
    (hd : IsZero (P.complex.X 3)) (r : R) (hr : r ≠ 0) (hM : ∀ x : M, r • x = 0) :
    Module.finrank R (P.complex.X 1) =
      Module.finrank R (P.complex.X 2) + Module.finrank R (P.complex.X 0) := by
  let : Subsingleton (LocalizedModule (nonZeroDivisors R) M) :=
    LocalizedModule.subsingleton_iff.mpr (fun x =>
      ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, hM x⟩)
  let : Subsingleton (FractionRing R ⊗[R] M) :=
    (LocalizedModule.equivTensorProduct (nonZeroDivisors R) M).symm.injective.subsingleton
  have he := Generic.RankEuler.alternating_rank R (FractionRing R) M P hP 2 hd
  rw [Module.finrank_zero_of_subsingleton] at he
  norm_num [Finset.sum_range_succ] at he
  have he' : (Module.finrank R (P.complex.X 1) : ℚ) =
      (Module.finrank R (P.complex.X 2) : ℚ) + (Module.finrank R (P.complex.X 0) : ℚ) := by
    linarith
  exact_mod_cast he'

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionRankBalance
