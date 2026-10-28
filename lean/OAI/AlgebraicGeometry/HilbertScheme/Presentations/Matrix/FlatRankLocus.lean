import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.StalkCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FixedRankCokernel

/-! # Flat Rank Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian

noncomputable section

/-! The actual scheme representing stalkwise flatness and prescribed rank of
the cokernel of a finite matrix. The construction and universal property work
over arbitrary test schemes, with no noetherian assumption. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι μ ν : Type u} [Fintype ι] [Fintype μ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

def matrixAtStalk {T : Over S} (x : T ⟶ M) (t : T.left) :
    Matrix ν μ (T.left.presheaf.stalk t) :=
  A.map ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom)

/-- The cokernel itself is flat at every stalk, and its rank plus the pivot
size is the number of rows. This also correctly excludes impossible pivot sizes. -/
def MatrixCokernelFlatRank {T : Over S} (x : T ⟶ M) : Prop :=
  ∀ t : T.left,
    Module.Flat (T.left.presheaf.stalk t)
      ((ν → T.left.presheaf.stalk t) ⧸ (Matrix.toLin' (matrixAtStalk M A x t)).range) ∧
    Module.finrank (T.left.presheaf.stalk t)
      ((ν → T.left.presheaf.stalk t) ⧸ (Matrix.toLin' (matrixAtStalk M A x t)).range) +
        Fintype.card ι = Fintype.card ν

theorem matrixCokernelFlatRank_iff_stalk {T : Over S} (x : T ⟶ M) :
    MatrixCokernelFlatRank (ι := ι) M A x ↔ MatrixRank.StalkLifting.Grassmannian.matrixRankStalkCondition (ι := ι) M A x := by
  constructor
  · intro h t
    obtain ⟨a, b, hu, hz⟩ := (Local.FixedRankCokernel.Grassmannian.local_cokernel_flat_fixed_rank_iff (ι := ι) (matrixAtStalk M A x t)).mp (h t)
    exact ⟨⟨a, b⟩, (MatrixPivot.Condition.Grassmannian.fullMatrixPivotCondition_iff A a b _).mpr ⟨hu, hz⟩⟩
  · intro h t
    obtain ⟨p, hp⟩ := h t
    have h' := (MatrixPivot.Condition.Grassmannian.fullMatrixPivotCondition_iff A p.1 p.2 _).mp hp
    exact (Local.FixedRankCokernel.Grassmannian.local_cokernel_flat_fixed_rank_iff (ι := ι) (matrixAtStalk M A x t)).mpr
      ⟨p.1, p.2, h'.1, h'.2⟩

theorem matrixCokernelFlatRank_iff_local {T : Over S} (x : T ⟶ M) :
    MatrixCokernelFlatRank (ι := ι) M A x ↔ MatrixRank.Representation.Grassmannian.matrixRankLocalCondition (ι := ι) M A x :=
  (matrixCokernelFlatRank_iff_stalk M A x).trans (MatrixRank.StalkCriterion.Grassmannian.matrixRank_stalk_iff_local M A x)

def matrixFlatRankSubfunctor : Subfunctor (yoneda.obj M) where
  obj _T := {x | MatrixCokernelFlatRank (ι := ι) M A x}
  map a x hx := (matrixCokernelFlatRank_iff_local M A _).mpr
    ((MatrixRank.Representation.Grassmannian.matrixRankSubfunctor (ι := ι) M A).map a ((matrixCokernelFlatRank_iff_local M A x).mp hx))

theorem matrixFlatRankSubfunctor_eq :
    matrixFlatRankSubfunctor (ι := ι) M A = MatrixRank.Representation.Grassmannian.matrixRankSubfunctor (ι := ι) M A := by
  ext T x
  exact matrixCokernelFlatRank_iff_local M A x

/-- Unconditional functorial representability of the flat fixed-rank cokernel
locus. The representing morphism is the constructed glued monomorphism. -/
theorem matrix_flat_fixed_rank_locus_representable :
    ∃ (Z : Over S) (j : Z ⟶ M), Mono j ∧
      ∃ e : yoneda.obj Z ≅ (matrixFlatRankSubfunctor (ι := ι) M A).toFunctor,
        e.hom ≫ (matrixFlatRankSubfunctor (ι := ι) M A).ι = yoneda.map j := by
  rw [matrixFlatRankSubfunctor_eq]
  exact ⟨MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M A, MatrixRank.Data.Grassmannian.matrixRankParameterMap M A, inferInstance,
    MatrixRank.Representation.Grassmannian.matrixRankRepresentation M A, MatrixRank.Representation.Grassmannian.matrixRankRepresentation_inclusion M A⟩

theorem matrixCokernelFlatRank_iff_unique_lift {T : Over S} (x : T ⟶ M) :
    MatrixCokernelFlatRank (ι := ι) M A x ↔
      ∃! y : T ⟶ MatrixRank.Data.Grassmannian.matrixRankOver (ι := ι) M A, y ≫ MatrixRank.Data.Grassmannian.matrixRankParameterMap M A = x :=
  (matrixCokernelFlatRank_iff_local M A x).trans (MatrixRank.Representation.Grassmannian.matrixRankLocalCondition_iff_lift M A x)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian
