import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.StalkLifting
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.GermNaturality

/-! # Stalk Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.StalkCriterion.Grassmannian

noncomputable section

/-! The represented local matrix-rank condition is equivalent to the explicit
pivot equations in every stalk. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

theorem matrixRank_stalk_of_local {T : Over S} (x : T ⟶ M)
    (hx : Representation.Grassmannian.matrixRankLocalCondition (ι := ι) M A x) :
    StalkLifting.Grassmannian.matrixRankStalkCondition (ι := ι) M A x := by
  obtain ⟨U, hU⟩ := (Equations.Grassmannian.matrixRankLocalCondition_iff_equations M A x).mp hx
  intro t
  let i := U.idx t
  obtain ⟨v, hv⟩ := U.covers t
  obtain ⟨p, hp⟩ := hU i
  refine ⟨p, ?_, ?_⟩
  · change IsUnit (T.left.presheaf.Γgerm t (x.left.appTop (A.submatrix p.2 p.1).det))
    rw [← hv]
    apply (isUnit_map_iff ((U.f i).stalkMap v).hom _).mp
    rw [Global.GermNaturality.global_germ_appTop]
    exact hp.1.map ((U.X i).presheaf.Γgerm v).hom
  · intro q
    change T.left.presheaf.Γgerm t (x.left.appTop
      (MatrixPivot.Cokernel.Grassmannian.pivotResidual (A.submatrix p.2 p.1) (A.submatrix p.2 id) (A.submatrix id p.1) A q.1 q.2)) = 0
    rw [← hv]
    apply (ConcreteCategory.bijective_of_isIso ((U.f i).stalkMap v)).1
    rw [map_zero, Global.GermNaturality.global_germ_appTop]
    change (U.X i).presheaf.Γgerm v ((U.f i ≫ x.left).appTop
      (MatrixPivot.Cokernel.Grassmannian.pivotResidual (A.submatrix p.2 p.1) (A.submatrix p.2 id) (A.submatrix id p.1) A q.1 q.2)) = 0
    rw [hp.2 q, map_zero]

theorem matrixRank_stalk_iff_local [Finite μ] [Finite ν]
    {T : Over S} (x : T ⟶ M) :
    StalkLifting.Grassmannian.matrixRankStalkCondition (ι := ι) M A x ↔ Representation.Grassmannian.matrixRankLocalCondition (ι := ι) M A x :=
  ⟨StalkLifting.Grassmannian.matrixRank_local_of_stalk M A x, matrixRank_stalk_of_local M A x⟩

theorem matrixRankRepresentation_stalks [Finite μ] [Finite ν]
    {T : Over S} (x : T ⟶ M) :
    StalkLifting.Grassmannian.matrixRankStalkCondition (ι := ι) M A x ↔
      ∃! y : T ⟶ Data.Grassmannian.matrixRankOver (ι := ι) M A, y ≫ Data.Grassmannian.matrixRankParameterMap M A = x :=
  (matrixRank_stalk_iff_local M A x).trans (Representation.Grassmannian.matrixRankLocalCondition_iff_lift M A x)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.StalkCriterion.Grassmannian
