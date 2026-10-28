import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Equations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.StalkEquations

/-! # Stalk Lifting -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.StalkLifting.Grassmannian

noncomputable section

/-! Stalkwise pivot conditions give unique points of the constructed matrix-rank
scheme. Finiteness of the presentation supplies a common neighborhood for all
residual equations; no noetherian hypothesis is used. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

def matrixRankStalkCondition {T : Over S} (x : T ⟶ M) : Prop :=
  ∀ t : T.left, ∃ p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν,
    MatrixPivot.Locus.Grassmannian.matrixPivotCondition (A.submatrix p.2 p.1) (A.submatrix p.2 id)
      (A.submatrix id p.1) A ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom)

theorem matrixRank_local_of_stalk [Finite μ] [Finite ν]
    {T : Over S} (x : T ⟶ M) (hx : matrixRankStalkCondition (ι := ι) M A x) :
    Representation.Grassmannian.matrixRankLocalCondition (ι := ι) M A x := by
  have h (t : T.left) : ∃ (U : T.left.Opens), t ∈ U ∧ ∃ p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν,
      MatrixPivot.Locus.Grassmannian.matrixPivotCondition (A.submatrix p.2 p.1) (A.submatrix p.2 id)
        (A.submatrix id p.1) A (U.ι ≫ x.left).appTop.hom := by
    obtain ⟨p, hp⟩ := hx t
    obtain ⟨U, htU, hunit, hzero⟩ := Presentations.Finite.StalkEquations.finite_unit_zero_neighborhood
      (x.left.appTop (A.submatrix p.2 p.1).det)
      (fun q : ν × μ => x.left.appTop
        (MatrixPivot.Cokernel.Grassmannian.pivotResidual (A.submatrix p.2 p.1) (A.submatrix p.2 id)
          (A.submatrix id p.1) A q.1 q.2)) t hp.1 hp.2
    exact ⟨U, htU, p, hunit, hzero⟩
  choose U htU p hp using h
  let C : T.left.OpenCover.{u} := {
    I₀ := T.left
    X t := (U t).toScheme
    f t := (U t).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun t => ⟨t, by simpa using htU t⟩, inferInstance⟩ }
  apply (Equations.Grassmannian.matrixRankLocalCondition_iff_equations M A x).mpr
  exact ⟨C, fun t => ⟨p t, hp t⟩⟩

theorem matrixRank_lift_of_stalk [Finite μ] [Finite ν]
    {T : Over S} (x : T ⟶ M) (hx : matrixRankStalkCondition (ι := ι) M A x) :
    ∃! y : T ⟶ Data.Grassmannian.matrixRankOver (ι := ι) M A, y ≫ Data.Grassmannian.matrixRankParameterMap M A = x :=
  (Representation.Grassmannian.matrixRankLocalCondition_iff_lift M A x).mp (matrixRank_local_of_stalk M A x hx)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.StalkLifting.Grassmannian
