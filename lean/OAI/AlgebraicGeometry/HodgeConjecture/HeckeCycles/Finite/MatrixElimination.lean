import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockMatrixUnits

/-! # Matrix Elimination -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixElimination.CM

/-! Finite adelic Gaussian elimination, using actual unit pivots. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ElementaryMatrixUnits.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockMatrixUnits.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockMatrixUnits.CM.UnitPivotFactorization

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_row_correction (A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) (i : I) :
    ∃ c : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf, c i = 0 ∧ IsUnit (A.val i i + ∑ j, c j * A.val j i) := by
  have hdec : ‹DecidableEq I› = Classical.decEq I := Subsingleton.elim _ _
  cases hdec
  exact MatrixPivot.CM.exists_row_correction A i

theorem mem_of_smaller (H : Subgroup (Matrix (I ⊕ Unit) (I ⊕ Unit) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ)
    (hSym : ∀ A : (Matrix (I ⊕ Unit) (I ⊕ Unit) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ, A.val.IsSymm → A ∈ H)
    (hLeft : ∀ A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ, BlockMatrixUnits.CM.embedLeft A ∈ H)
    (M : (Matrix (I ⊕ Unit) (I ⊕ Unit) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ) : M ∈ H := by
  obtain ⟨c, hc, hp⟩ := exists_row_correction M (Sum.inr ())
  let E := ElementaryMatrixUnits.CM.rowUnit (Sum.inr ()) c hc
  have hE : E ∈ H := ElementaryMatrixUnits.CM.rowUnit_mem H hSym _ _ _
  have hEM : E * M ∈ H := by
    apply BlockMatrixUnits.CM.UnitPivotFactorization.mem_of_unit_pivot H hSym hLeft
    change IsUnit (((ElementaryMatrixUnits.CM.rowUnit (Sum.inr ()) c hc).val * M.val) (Sum.inr ()) (Sum.inr ()))
    rw [ElementaryMatrixUnits.CM.rowUnit_mul_pivot]
    exact hp
  have he := H.mul_mem (H.inv_mem hE) hEM
  simpa only [inv_mul_cancel_left] using he

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixElimination.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixElimination.CM.SymmetricGeneration

/-! Actual general linear groups over the finite adeles are generated
by symmetric invertible matrices. The proof uses adelic unit pivots
and induction on the matrix dimension. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockMatrixUnits.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixElimination.CM

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def GeneratedBySymmetric (I : Type*) [Fintype I] [DecidableEq I] : Prop :=
  ∀ H : Subgroup (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ,
    (∀ A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ, A.val.IsSymm → A ∈ H) → H = ⊤

theorem of_equiv (e : I ≃ J) (hJ : GeneratedBySymmetric J) : GeneratedBySymmetric I := by
  let F : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ ≃* (Matrix J J RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ :=
    Units.mapEquiv (Matrix.reindexRingEquiv RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf e).toMulEquiv
  intro H hSym
  let K := H.comap F.symm.toMonoidHom
  have hK : K = ⊤ := by
    apply hJ
    intro A hA
    apply hSym (F.symm A)
    exact hA.reindex e.symm
  apply top_unique
  intro A _
  have hmem : F A ∈ K := by rw [hK]; trivial
  change F.symm (F A) ∈ H at hmem
  simpa only [F.symm_apply_apply] using hmem

theorem fin_generation (n : ℕ) : GeneratedBySymmetric (Fin n) := by
  induction n with
  | zero =>
    intro H hSym
    apply top_unique
    intro A _
    apply hSym A
    ext i
    exact Fin.elim0 i
  | succ n ih =>
    have e : Fin (n + 1) ≃ Fin n ⊕ Unit := Fintype.equivOfCardEq (by simp)
    apply of_equiv e
    intro H hSym
    apply top_unique
    intro M _
    apply mem_of_smaller H hSym _ M
    intro A
    have hK : H.comap (BlockMatrixUnits.CM.embedLeft (J := Unit)) = ⊤ := by
      apply ih
      intro B hB
      exact hSym _ (BlockMatrixUnits.CM.embedLeft_symmetric B hB)
    change A ∈ H.comap (BlockMatrixUnits.CM.embedLeft (J := Unit))
    rw [hK]
    trivial

theorem generated_by_symmetric (H : Subgroup (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ)
    (hSym : ∀ A : (Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ, A.val.IsSymm → A ∈ H) : H = ⊤ :=
  of_equiv (Fintype.equivFin I) (fin_generation (Fintype.card I)) H hSym

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixElimination.CM.SymmetricGeneration

end

end OAI
