import OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeMatrixChange
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteSpecialLinearCorrection

/-! # Adelic Lattice Rational Frame -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeRationalFrame

noncomputable section

/-! Every lattice from a finite-adelic special-linear group point
has a rational determinant-one frame. This fixes its covolume without
assuming strong approximation for the smaller algebraic group. -/

open scoped Classical _root_.NumberField

variable {F : Type} [Field F] [NumberField F] {n : ℕ} [Nontrivial (Fin n)]

theorem finiteAdelicGroupLattice_rational_frame (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) :
    ∃ b : Matrix.SpecialLinearGroup (Fin n) F,
      FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g) =
        (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).module.map
          ((Matrix.SpecialLinearGroup.toLin' b).toLinearMap.restrictScalars (𝓞 F)) := by
  let H := SpecialLinearAdeles.specialLinearMatrixGroup F n
  let a := FiniteSpecialLinearCorrection.finiteAdelicToSpecialLinear G g
  obtain ⟨b, hb⟩ := FiniteSpecialLinearCorrection.finiteSpecialLinear_integral_correction a
  let c := a * FiniteAdelicComparison.diagonalFiniteAdelic H b
  let C := FiniteAdelicMatrices.finiteAdelicMatrixUnitHom H c
  have hc := (FiniteSpecialLinearCorrection.finiteAdelicMatrix_integral_iff H c).mp hb
  have hCi : C.inv = FiniteAdelicMatrices.finiteAdelicMatrix H c⁻¹ := by
    change ((FiniteAdelicMatrices.finiteAdelicMatrixUnitHom H c)⁻¹).val = _
    rw [← map_inv]
    rfl
  have hstd := AdelicLatticeMatrixChange.finiteAdelicMatrixLattice_integral_unit_eq_standard C hc.1
    (fun i j => hCi ▸ hc.2 i j)
  have hC : C.val = FiniteAdelicMatrices.finiteAdelicMatrix G g * b.val.val.map (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F)) := by
    calc
      C.val = FiniteAdelicMatrices.finiteAdelicMatrix H a * FiniteAdelicMatrices.finiteAdelicMatrix H (FiniteAdelicComparison.diagonalFiniteAdelic H b) :=
        map_mul (FiniteAdelicMatrices.finiteAdelicMatrixHom H) a (FiniteAdelicComparison.diagonalFiniteAdelic H b)
      _ = FiniteAdelicMatrices.finiteAdelicMatrix G g * b.val.val.map (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F)) :=
        congrArg₂ (· * ·) (FiniteSpecialLinearCorrection.finiteAdelicToSpecialLinear_matrix G g) (FiniteAdelicComparison.finiteAdelicMatrix_diagonal H b)
  rw [hC, AdelicLatticeMatrixChange.finiteAdelicMatrixLattice_mul_rational] at hstd
  let f := (Matrix.SpecialLinearGroup.toLin' b.val).toLinearMap.restrictScalars (𝓞 F)
  have hf : Function.Surjective f := (Matrix.SpecialLinearGroup.toLin' b.val).surjective
  change (FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g)).comap f = (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).module at hstd
  refine ⟨b.val, ?_⟩
  calc
    FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g) =
        ((FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g)).comap f).map f :=
      (Submodule.map_comap_eq_of_surjective hf _).symm
    _ = (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).module.map f := congrArg (Submodule.map f) hstd

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeRationalFrame
