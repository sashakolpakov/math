import OAI.NumberTheory.Quaternion.Arithmetic.SemisimpleFiniteGalois
import OAI.NumberTheory.Quaternion.Arithmetic.ConjugateEigenbasis
import OAI.NumberTheory.Quaternion.Arithmetic.GaloisTraceMatrix
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.TangentExtension

/-! # Semisimple Trace Span -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SemisimpleTraceSpan

noncomputable section

/-! Every semisimple infinitesimal matrix over the base field is
spanned by traces of integrable integer-weight directions over one
finite Galois extension. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.TangentExtension.Construction

attribute [local instance] LieRing.ofAssociativeRing

theorem semisimple_mem_span_finiteGalois_traces
    {F : Type} [Field F] [CharZero F] {n : ℕ} [Nonempty (Fin n)]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hG : G.IsGeometricallyConnected)
    (S : Matrix (Fin n) (Fin n) F) (hLie : S ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    (hS : Module.End.IsSemisimple (Matrix.toLin' S)) :
    ∃ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
      S ∈ Submodule.span F {Z | ∃ a : L, ∃ Y ∈ IntegralSemisimpleDirections.integralPolynomialDirections
        (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F L)) (S.map (algebraMap F L)),
          Z = GaloisTraceMatrix.fieldTraceMatrix (F := F) (a • Y)} := by
  obtain ⟨L, B, w, hdiag⟩ := SemisimpleFiniteGalois.semisimple_matrix_finiteGalois_diagonalization S hS
  have hL : S.map (algebraMap F L) ∈
      ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F L)) := by
    change S.map (algebraMap F L) ∈
      (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F L))).toSubmodule
    rw [ArithmeticGroups.Lattices.Infinitesimal.TangentExtension.Construction.infinitesimalStabilizer_eq_span_base G hG]
    exact Submodule.subset_span ⟨S, hLie, rfl⟩
  refine ⟨L, GaloisTraceMatrix.fieldTraceMatrix_mem_span_of_mem_span S _ ?_⟩
  exact ConjugateEigenbasis.conjugate_diagonal_mem_span_integral_polynomial_directions
    (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F L)) _ B w hdiag hL

end

end OAI.NumberTheory.Quaternion.Arithmetic.SemisimpleTraceSpan
