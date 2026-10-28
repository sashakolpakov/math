import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.MatrixKernelGrassmannian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismFromAffineTests
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankAffineCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineQuotientPoint

/-! # Scheme Flat Matrix Grassmannian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeFlatMatrixGrassmannian

noncomputable section

/-! A global matrix satisfying the actual flat-cokernel rank condition
defines a scheme morphism to the relative Grassmannian. Its value on
every affine test is the exact kernel of the pulled-back matrix. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι μ ν : Type u} [Fintype ι] [Fintype μ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]
variable {S : Scheme.{u}} (M : Over S) (F : Matrix ν μ Γ(M.left, ⊤))

def affineMatrixTestOver (R : CommRingCat.{u}) (x : Spec R ⟶ M.left) :
    Over.mk (x ≫ M.hom) ⟶ M := Over.homMk x rfl

def affineSchemeMatrixCoefficients (R : CommRingCat.{u}) (x : Spec R ⟶ M.left) : Matrix ν μ R :=
  HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M F R (affineMatrixTestOver M R x)

omit [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν] in
theorem affineSchemeMatrixCoefficients_specMap (R A : CommRingCat.{u})
    (φ : R →+* A) (x : Spec R ⟶ M.left) :
    affineSchemeMatrixCoefficients M F A (Spec.map (CommRingCat.ofHom φ) ≫ x) =
      (affineSchemeMatrixCoefficients M F R x).map φ := by
  ext i j
  simp only [affineSchemeMatrixCoefficients, HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients, affineMatrixTestOver,
    Matrix.map_apply, RingHom.comp_apply]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) (x.appTop (F i j))

variable (H : HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ι) M F (𝟙 M))

include H in
theorem affineSchemeMatrix_flatRank (R : CommRingCat.{u}) (x : Spec R ⟶ M.left) :
    Module.Flat R ((ν → R) ⧸ (Matrix.toLin' (affineSchemeMatrixCoefficients M F R x)).range) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R)
        ((ν → R) ⧸ (Matrix.toLin' (affineSchemeMatrixCoefficients M F R x)).range) p +
          Fintype.card ι = Fintype.card ν := by
  have hx : HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ι) M F (affineMatrixTestOver M R x) := by
    have h := (HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.matrixFlatRankSubfunctor (ι := ι) M F).map (affineMatrixTestOver M R x).op H
    change HilbertScheme.Presentations.Matrix.FlatRankLocus.Grassmannian.MatrixCokernelFlatRank (ι := ι) M F (affineMatrixTestOver M R x ≫ 𝟙 M) at h
    simpa only [Category.comp_id] using h
  exact (HilbertConstruction.Matrix.RankAffineCriterion.matrixRank_affine_iff M F R (affineMatrixTestOver M R x)).mp hx

def affineMatrixKernelPoint (R : CommRingCat.{u}) (x : Spec R ⟶ M.left) :
    Module.Grassmannian R (μ → R) (Fintype.card ι) :=
  HilbertConstruction.Flat.MatrixKernelGrassmannian.flatMatrixKernelGrassmannian (affineSchemeMatrixCoefficients M F R x) (Fintype.card ι)
    (affineSchemeMatrix_flatRank M F H R x).1 (affineSchemeMatrix_flatRank M F H R x).2

theorem affineMatrixKernelPoint_natural (R A : CommRingCat.{u})
    (φ : R →+* A) (x : Spec R ⟶ M.left) :
    HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ (affineMatrixKernelPoint M F H R x) =
      affineMatrixKernelPoint M F H A (Spec.map (CommRingCat.ofHom φ) ≫ x) := by
  apply Module.Grassmannian.ext
  change HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ (Matrix.toLin' (affineSchemeMatrixCoefficients M F R x)).ker =
    (Matrix.toLin' (affineSchemeMatrixCoefficients M F A (Spec.map (CommRingCat.ofHom φ) ≫ x))).ker
  rw [affineSchemeMatrixCoefficients_specMap]
  exact HilbertConstruction.Flat.CokernelKernelBaseChange.matrix_kernel_baseChange_of_flat_cokernel φ _ (affineSchemeMatrix_flatRank M F H R x).1

def schemeFlatMatrixAffineData :
    MorphismFromAffineTests.AffineTestMorphismData M.left (HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianScheme (ι := ι) (ν := μ) S) where
  app R x := (HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint (x ≫ M.hom) (affineMatrixKernelPoint M F H R x)).left
  naturality R A f x := by
    let φ : R →+* A := (Spec.preimage f).hom
    have hf : Spec.map (CommRingCat.ofHom φ) = f := Spec.map_preimage f
    have hp := congrArg Over.Hom.left
      (HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint_natural (x ≫ M.hom) φ (affineMatrixKernelPoint M F H R x))
    rw [affineMatrixKernelPoint_natural] at hp
    replace hp := hp.symm
    change (HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint (Spec.map (CommRingCat.ofHom φ) ≫ (x ≫ M.hom))
      (affineMatrixKernelPoint M F H A (Spec.map (CommRingCat.ofHom φ) ≫ x))).left =
        Spec.map (CommRingCat.ofHom φ) ≫
          (HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint (x ≫ M.hom) (affineMatrixKernelPoint M F H R x)).left at hp
    rw [← hf]
    change HilbertScheme.Presentations.Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap A (affineMatrixKernelPoint M F H A (Spec.map (CommRingCat.ofHom φ) ≫ x)) ≫
      HilbertScheme.Presentations.Grassmannian.BaseMap.grassmannianBaseMap ((Spec.map (CommRingCat.ofHom φ) ≫ x) ≫ M.hom) =
        Spec.map (CommRingCat.ofHom φ) ≫
          (HilbertScheme.Presentations.Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap R (affineMatrixKernelPoint M F H R x) ≫ HilbertScheme.Presentations.Grassmannian.BaseMap.grassmannianBaseMap (x ≫ M.hom))
    rw [Category.assoc (Spec.map (CommRingCat.ofHom φ)) x M.hom]
    exact hp

def schemeFlatMatrixKernelMap : M.left ⟶ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianScheme (ι := ι) (ν := μ) S :=
  (schemeFlatMatrixAffineData M F H).toHom

theorem schemeFlatMatrixKernelMap_affine (R : CommRingCat.{u}) (x : Spec R ⟶ M.left) :
    x ≫ schemeFlatMatrixKernelMap M F H =
      (HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint (x ≫ M.hom) (affineMatrixKernelPoint M F H R x)).left :=
  (schemeFlatMatrixAffineData M F H).toHom_on_affine R x

theorem schemeFlatMatrixKernelMap_over :
    schemeFlatMatrixKernelMap M F H ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianStructureMap S = M.hom := by
  apply M.left.affineOpenCover.openCover.hom_ext
  intro i
  rw [← Category.assoc, schemeFlatMatrixKernelMap_affine]
  exact (HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint (M.left.affineOpenCover.f i ≫ M.hom)
    (affineMatrixKernelPoint M F H (M.left.affineOpenCover.X i) (M.left.affineOpenCover.f i))).w

def schemeFlatMatrixKernelOver : M ⟶ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := μ) S :=
  Over.homMk (schemeFlatMatrixKernelMap M F H) (schemeFlatMatrixKernelMap_over M F H)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeFlatMatrixGrassmannian
