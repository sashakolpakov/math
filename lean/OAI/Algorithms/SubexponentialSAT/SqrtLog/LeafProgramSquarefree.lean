import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramProjection
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeJet

namespace OAI.Algorithms

/-! The sparse-hash circuit projection theorem instantiated at the actual
Boolean-support U/Z jet algebra. This ties local circuit evaluation to the
same source polynomial used by the global interpolation proof. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

variable {V C R : Type*} [DecidableEq V] [CommRing R]

noncomputable abbrev squarefreeAlgebra (t J : ℕ) : Algebra (Squarefree.Jet V R) :=
  projectedAlgebra (Squarefree.canonical t J)

theorem squarefree_rowValue (t J : ℕ)
    (decode : C → Squarefree.Jet V R) (value : V → Squarefree.Jet V R)
    (terms : SparseRow V C) :
    rowValue (squarefreeAlgebra t J)
      (fun c => Squarefree.canonical t J (decode c))
      (fun v => Squarefree.canonical t J (value v)) terms =
      Squarefree.canonical t J
        (MvPolynomial.eval value (rowPolynomial decode terms)) := by
  simpa only [squarefreeAlgebra] using
    (rowValue_projected_eq_eval (R := Squarefree.Jet V R) (Squarefree.canonical t J)
      (Squarefree.canonical_mul t J) decode value terms)

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
