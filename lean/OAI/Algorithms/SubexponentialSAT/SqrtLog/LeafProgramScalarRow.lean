import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFolded

namespace OAI.Algorithms

/-! Flat ring coefficients may scale sparse dictionaries directly. They need
not first be serialized as a singleton sparse dictionary. This interface is
used by the native weighted-clause interpreter. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {V R : Type*} [DecidableEq V] [CommRing R]
variable {vars : Finset V} {t J : ℕ}

noncomputable def scalarJet (c : R) : Jet V R := Sparse.atom Index.origin c

/-- Direct scalar scaling has precisely the truncated-multiplication meaning
used by the generic row fold. -/
theorem stored_scale_correct (c : R) (a : Moments.Stored (R := R) vars t J) :
    (Moments.Stored.scale c a).denote =
      (squarefreeAlgebra t J).mul (Squarefree.canonical t J (scalarJet c)) a.denote := by
  have hcanon := (a.valid.scale c).canonical
  rw [Sparse.denote_scale] at hcanon
  have hprod := Squarefree.canonical_mul t J (scalarJet (V := V) c) a.denote
  rw [a.canonical] at hprod
  change Sparse.denote (Sparse.scale c a.data) =
    Squarefree.canonical t J (Squarefree.canonical t J (scalarJet c) * a.denote)
  rw [Sparse.denote_scale]
  change Sparse.atom Index.origin c * a.denote =
    Squarefree.canonical t J (Squarefree.canonical t J (scalarJet c) * a.denote)
  exact hcanon.symm.trans hprod.symm

/-- The native left fold with flat scalar weights denotes the same source
polynomial as the generic weighted sparse-row evaluator. -/
theorem scalar_rowFold_source (t J : ℕ) (value : V → Jet V R)
    (terms : SparseRow V R) :
    rowFoldValue (squarefreeAlgebra t J)
      (fun c => Squarefree.canonical t J (scalarJet c))
      (fun v => Squarefree.canonical t J (value v)) terms 0 =
        Squarefree.canonical t J (MvPolynomial.eval value (rowPolynomial (R := Jet V R) (scalarJet (V := V)) terms)) := by
  have h := rowFoldValue_projected_zero (Squarefree.canonical t J)
    (Squarefree.canonical_mul t J) (scalarJet (V := V)) value terms
  exact h.trans (squarefree_rowValue t J (scalarJet (V := V)) value terms)

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
