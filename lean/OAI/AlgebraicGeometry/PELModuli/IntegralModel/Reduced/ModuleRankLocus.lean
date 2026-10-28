import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ModuleRankPresentation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.MatrixKernelRankLocus

/-! # Module Rank Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ModuleRankLocus

noncomputable section

/-! Every finitely presented module on an affine parameter chart
has an actual locally closed locus for its geometric fiber dimension.
The criterion classifies every reduced test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {S : Scheme.{0}} (M : Over S) (V : Type) [AddCommGroup V]
  [Module Γ(M.left, ⊤) V] [Module.FinitePresentation Γ(M.left, ⊤) V]

def HasGeometricModuleRank (r : ℕ) {T : Over S} (x : T ⟶ M) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T.left),
    letI : Algebra Γ(M.left, ⊤) k :=
      ((Scheme.ΓSpecIso (.of k)).hom.hom.comp (p ≫ x.left).appTop.hom).toAlgebra
    Module.finrank k (k ⊗[Γ(M.left, ⊤)] V) = r

theorem exists_reduced_test_module_rank_locus (r : ℕ) :
    ∃ (Z : Over S) (j : Z ⟶ M), IsImmersion j.left ∧ QuasiCompact j.left ∧
      ∀ (T : Over S) [IsReduced T.left] (x : T ⟶ M),
        HasGeometricModuleRank M V r x ↔ ∃! f : T ⟶ Z, f ≫ j = x := by
  obtain ⟨n, m, A, hA⟩ := Finite.ModuleRankPresentation.exists_finite_matrix_fiber_rank Γ(M.left, ⊤) V
  obtain ⟨Z, j, hj, hqc, hZ⟩ := MatrixKernelRankLocus.exists_reduced_test_matrix_kernel_rank_locus M A.transpose r
  refine ⟨Z, j, hj, hqc, ?_⟩
  intro T hT x
  rw [← hZ T x]
  have hf (k : Type) [Field k] (p : Spec (.of k) ⟶ T.left) :
      letI : Algebra Γ(M.left, ⊤) k :=
        ((Scheme.ΓSpecIso (.of k)).hom.hom.comp (p ≫ x.left).appTop.hom).toAlgebra
      Module.finrank k (k ⊗[Γ(M.left, ⊤)] V) =
        Module.finrank k (Matrix.toLin'
          (AbelianModuli.HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M A.transpose (.of k) (SubfunctorLocus.geometricTestMap x p))).ker := by
    let φ := (Scheme.ΓSpecIso (.of k)).hom.hom.comp (p ≫ x.left).appTop.hom
    let : Algebra Γ(M.left, ⊤) k := φ.toAlgebra
    exact (hA k φ).trans (MatrixKernelRankLocus.transpose_cokernel_finrank_eq_kernel (A.map φ).transpose)
  constructor
  · intro h k hk ha p
    exact (hf k p).symm.trans (h k p)
  · intro h k hk ha p
    exact (hf k p).trans (h k p)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ModuleRankLocus
