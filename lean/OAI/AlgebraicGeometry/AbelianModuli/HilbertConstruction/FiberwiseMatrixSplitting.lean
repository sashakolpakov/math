import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.SurjectivityBaseChange
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Module.Projective

/-! # Fiberwise Matrix Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberwiseMatrixSplitting

noncomputable section

/-! A finite matrix injective on all residue fields has an actual
left inverse over the original coefficient ring. Thus injection
persists under arbitrary, including nonflat, coefficient changes. -/
universe u
variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

theorem field_matrix_transpose_surjective_of_injective {K : Type u} [Field K]
    (F : Matrix ι ν K) (hF : Function.Injective (Matrix.toLin' F)) :
    Function.Surjective (Matrix.toLin' F.transpose) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  change F.transpose.rank = Module.finrank K (ν → K)
  rw [Matrix.rank_transpose]
  exact LinearMap.finrank_range_of_inj hF

theorem matrix_leftInverse_of_residueField_injective {R : Type u} [CommRing R]
    (F : Matrix ι ν R)
    (hF : ∀ p : PrimeSpectrum R,
      Function.Injective (Matrix.toLin' (F.map (algebraMap R p.asIdeal.ResidueField)))) :
    ∃ B : Matrix ν ι R, B * F = 1 := by
  have hsurj : Function.Surjective (Matrix.toLin' F.transpose) := by
    apply HilbertConstruction.Matrix.SurjectivityBaseChange.matrix_surjective_of_residueFields
    intro p
    exact field_matrix_transpose_surjective_of_injective _ (hF p)
  obtain ⟨g, hg⟩ := (Matrix.toLin' F.transpose).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  have hmat : F.transpose * LinearMap.toMatrix' g = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using
      congrArg (fun f : (ν → R) →ₗ[R] (ν → R) => LinearMap.toMatrix' f) hg
  refine ⟨(LinearMap.toMatrix' g).transpose, ?_⟩
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using
    congrArg Matrix.transpose hmat

theorem matrix_injective_all_baseChanges_of_residueField_injective
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (F : Matrix ι ν R)
    (hF : ∀ p : PrimeSpectrum R,
      Function.Injective (Matrix.toLin' (F.map (algebraMap R p.asIdeal.ResidueField)))) :
    Function.Injective (Matrix.toLin' (F.map φ)) := by
  obtain ⟨B, hB⟩ := matrix_leftInverse_of_residueField_injective F hF
  have hBA : B.map φ * F.map φ = 1 := by
    calc
      B.map φ * F.map φ = (B * F).map φ := Matrix.map_mul.symm
      _ = (1 : Matrix ν ν R).map φ := congrArg (fun M : Matrix ν ν R => M.map φ) hB
      _ = 1 := Matrix.map_one φ (map_zero φ) (map_one φ)
  have hlin : (Matrix.toLin' (B.map φ)).comp (Matrix.toLin' (F.map φ)) = LinearMap.id := by
    rw [← Matrix.toLin'_mul, hBA, Matrix.toLin'_one]
  have hl : Function.LeftInverse (Matrix.toLin' (B.map φ)) (Matrix.toLin' (F.map φ)) :=
    fun x => LinearMap.congr_fun hlin x
  exact hl.injective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberwiseMatrixSplitting
