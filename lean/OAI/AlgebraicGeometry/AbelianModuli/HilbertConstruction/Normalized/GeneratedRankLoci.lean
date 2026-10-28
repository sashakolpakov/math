import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreeMatrices
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedMatrixRankLoci
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.DegreeFlatRank

/-! # Generated Rank Loci -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GeneratedRankLoci

noncomputable section

/-! On a normalized Grassmann chart, the finite generated-quotient condition is represented by an actual quasi-compact locally closed matrix locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) {n N : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (a : ι → ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N))
variable (Q : Matrix ι (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) Γ(M.left, ⊤))
variable (B : ℕ) (r : ℕ → ℕ)

def normalizedGeneratedRankSubfunctor : Subfunctor (yoneda.obj M) :=
  ⨅ d : Fin (B + 1), PrescribedMatrixRankLoci.prescribedMatrixRankSubfunctor M (DegreeMatrices.normalizedRetainedDegreeMatrix a Q d) (r d)

omit [DecidableEq ι] in
theorem normalizedGeneratedRank_immersion :
    HilbertScheme.Presentations.SubfunctorRepresentations.ImmersionRepresentable (normalizedGeneratedRankSubfunctor M a Q B r) :=
  PrescribedMatrixRankLoci.prescribedMatrixRanks_finite_intersection M
    (fun d : Fin (B + 1) =>
      HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert.DegreeRelationIndex (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) n (d.val - N))
    (fun d : Fin (B + 1) => HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n d)
    (fun d => DegreeMatrices.normalizedRetainedDegreeMatrix a Q d) (fun d => r d)

theorem normalizedGeneratedRank_affine_iff (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q)
    (R : CommRingCat.{u}) {f : Spec R ⟶ S} (x : Over.mk f ⟶ M)
    (U : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R N) (r N))
    (hU : U.toSubmodule = HomogeneousGenerators.normalizedHomogeneousRelations (HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M Q R x)) :
    x ∈ (normalizedGeneratedRankSubfunctor M a Q B r).obj (.op (Over.mk f)) ↔
      Generated.DegreeFlatRank.GeneratedDegreeFlatRank (B := B) U := by
  rw [normalizedGeneratedRankSubfunctor, Subfunctor.iInf_obj, Set.mem_iInter]
  change (∀ d : Fin (B + 1), x ∈
    (PrescribedMatrixRankLoci.prescribedMatrixRankSubfunctor M (DegreeMatrices.normalizedRetainedDegreeMatrix a Q d) (r d)).obj (.op (Over.mk f))) ↔
    ∀ d : Fin (B + 1), _
  apply forall_congr'
  intro d
  rw [PrescribedMatrixRankLoci.prescribedMatrixRank_affine_iff]
  let φ := (Scheme.ΓSpecIso R).hom.hom.comp x.left.appTop.hom
  have hm : HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M (DegreeMatrices.normalizedRetainedDegreeMatrix a Q d) R x =
      DegreeMatrices.normalizedRetainedDegreeMatrix a (HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M Q R x) d :=
    DegreeMatrices.normalizedRetainedDegreeMatrix_map a Q φ d
  rw [hm]
  let e := DegreeMatrices.normalizedRetainedDegreeMatrixCokernelEquiv a
    (HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M Q R x) (hQ.map φ) d
  rw [Module.Flat.equiv_iff e, Module.rankAtStalk_eq_of_equiv e, hU]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GeneratedRankLoci
