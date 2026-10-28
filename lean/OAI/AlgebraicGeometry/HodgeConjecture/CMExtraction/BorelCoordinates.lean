import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Unipotent

/-! # Borel Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BorelCoordinates.Iwasawa

noncomputable section

/-! Concrete diagonal and unipotent factorization of every actual GL3
Borel element, preserving the literal matrix entries. -/

open scoped Classical _root_.Matrix

variable {F : Type*} [Field F]

theorem gl3Borel_factorization (b : RepresentationTheory.Satake.GL3GL.Core.upperBorel F) :
    b.val = AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (RepresentationTheory.Satake.GL3GL.Core.diagonal F b) *
      Unipotent.Iwasawa.gl3Unipotent (b.val.val 0 1 / b.val.val 0 0)
        (b.val.val 0 2 / b.val.val 0 0) (b.val.val 1 2 / b.val.val 1 1) := by
  have h0 := RepresentationTheory.Satake.GL3GL.Core.diagonal_ne_zero F b 0
  have h1 := RepresentationTheory.Satake.GL3GL.Core.diagonal_ne_zero F b 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, RepresentationTheory.Satake.GL3GL.Core.diagonal, Unipotent.Iwasawa.gl3Unipotent, Matrix.diagonal_mul,
    b.property (show (0 : Fin 3) < 1 by decide),
    b.property (show (0 : Fin 3) < 2 by decide), b.property (show (1 : Fin 3) < 2 by decide)]
  all_goals field_simp

theorem gl3_diagonal_unipotent_commute (u : Fin 3 → Fˣ) (x y z : F) :
    AbelianScheme.TateComparison.HeckeKernel.diagonalUnit u * Unipotent.Iwasawa.gl3Unipotent x y z =
      Unipotent.Iwasawa.gl3Unipotent ((u 0 : F) / (u 1 : F) * x) ((u 0 : F) / (u 2 : F) * y)
        ((u 1 : F) / (u 2 : F) * z) * AbelianScheme.TateComparison.HeckeKernel.diagonalUnit u := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, Unipotent.Iwasawa.gl3Unipotent, Matrix.diagonal_mul, Matrix.mul_diagonal,
    div_mul_eq_mul_div, (u 1).ne_zero, (u 2).ne_zero]

theorem gl3_diagonal_mul (u v : Fin 3 → Fˣ) :
    AbelianScheme.TateComparison.HeckeKernel.diagonalUnit u * AbelianScheme.TateComparison.HeckeKernel.diagonalUnit v = AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => u i * v i) := by
  apply Units.ext
  simp [AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, Matrix.diagonal_mul_diagonal]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BorelCoordinates.Iwasawa
