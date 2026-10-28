import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberwiseMatrixSplitting
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Matrix Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MatrixSplitting

noncomputable section

/-! Geometric field tests suffice for a finite matrix to have a left
inverse over the original ring, retaining all nilpotent information. -/
open scoped _root_.Matrix
universe u
variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

omit [Fintype ι] [DecidableEq ι] in
theorem matrix_injective_of_injective_map {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : Function.Injective φ) (F : Matrix ι ν R)
    (hF : Function.Injective (Matrix.toLin' (F.map φ))) : Function.Injective (Matrix.toLin' F) := by
  intro x y hxy
  have hm : Matrix.toLin' (F.map φ) (φ ∘ x) = Matrix.toLin' (F.map φ) (φ ∘ y) := by
    funext i
    change (F.map φ *ᵥ (φ ∘ x)) i = (F.map φ *ᵥ (φ ∘ y)) i
    rw [← RingHom.map_mulVec, ← RingHom.map_mulVec]
    exact congrArg φ (congrFun hxy i)
  have h := hF hm
  funext i
  exact hφ (congrFun h i)

theorem matrix_leftInverse_of_geometric_injective {R : Type u} [CommRing R]
    (F : Matrix ι ν R)
    (hF : ∀ (K : Type u) [Field K] [IsAlgClosed K] (φ : R →+* K),
      Function.Injective (Matrix.toLin' (F.map φ))) : ∃ B : Matrix ν ι R, B * F = 1 := by
  apply FiberwiseMatrixSplitting.matrix_leftInverse_of_residueField_injective F
  intro p
  let K := p.asIdeal.ResidueField
  let L := AlgebraicClosure K
  let φ : R →+* L := (algebraMap K L).comp (algebraMap R K)
  apply matrix_injective_of_injective_map (algebraMap K L) (RingHom.injective _) (F.map (algebraMap R K))
  exact hF L φ

theorem matrix_injective_all_baseChanges_of_geometric_injective
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (F : Matrix ι ν R)
    (hF : ∀ (K : Type u) [Field K] [IsAlgClosed K] (ψ : R →+* K),
      Function.Injective (Matrix.toLin' (F.map ψ))) :
    Function.Injective (Matrix.toLin' (F.map φ)) := by
  obtain ⟨B, hB⟩ := matrix_leftInverse_of_geometric_injective F hF
  have hBA : B.map φ * F.map φ = 1 := by
    calc
      B.map φ * F.map φ = (B * F).map φ := Matrix.map_mul.symm
      _ = (1 : Matrix ν ν R).map φ := congrArg (fun M : Matrix ν ν R => M.map φ) hB
      _ = 1 := Matrix.map_one φ (map_zero φ) (map_one φ)
  have hlin : (Matrix.toLin' (B.map φ)).comp (Matrix.toLin' (F.map φ)) = LinearMap.id := by
    rw [← Matrix.toLin'_mul, hBA, Matrix.toLin'_one]
  have hleft : Function.LeftInverse (Matrix.toLin' (B.map φ)) (Matrix.toLin' (F.map φ)) :=
    fun x => LinearMap.congr_fun hlin x
  exact hleft.injective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MatrixSplitting
