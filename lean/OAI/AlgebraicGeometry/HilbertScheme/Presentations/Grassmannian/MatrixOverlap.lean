import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.MatrixClassifyingEquations

/-! # Matrix Overlap -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.MatrixOverlap

noncomputable section

/-! Local matrices describing one Grassmannian morphism have identical quotient kernels on overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable (R : CommRingCat.{u})
variable {A C B : Type u} [CommRing A] [CommRing C] [CommRing B]
variable [Algebra R A] [Algebra R C] [Algebra R B]

theorem affine_classifying_common_kernel (φ : A →ₐ[R] B) (ψ : C →ₐ[R] B)
    (g : Spec R ⟶ Gluing.grassmannianScheme (ι := ι) (ν := ν) (Spec R))
    (a b : ι → ν) (Q : Matrix ι ν A) (K : Matrix ι ν C)
    (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) (hK : Normalized.Matrices.Grassmannian.IsNormalized b K)
    (hA : (Relative.AffinePoints.relativeAffineScheme R A).hom ≫ g = (Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A a Q hQ).left)
    (hC : (Relative.AffinePoints.relativeAffineScheme R C).hom ≫ g = (Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R C b K hK).left) :
    (Matrix.toLin' (Q.map φ.toRingHom)).ker = (Matrix.toLin' (K.map ψ.toRingHom)).ker := by
  let fA : Relative.AffinePoints.relativeAffineScheme R B ⟶ Relative.AffinePoints.relativeAffineScheme R A := (algSpec R).map (CommAlgCat.ofHom φ).op
  let fC : Relative.AffinePoints.relativeAffineScheme R B ⟶ Relative.AffinePoints.relativeAffineScheme R C := (algSpec R).map (CommAlgCat.ofHom ψ).op
  have he : fA ≫ Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A a Q hQ =
      fC ≫ Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R C b K hK := by
    apply (Over.forget (Spec R)).map_injective
    have heA : fA.left ≫ (Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A a Q hQ).left =
        (Relative.AffinePoints.relativeAffineScheme R B).hom ≫ g :=
      (congrArg (fun k => fA.left ≫ k) hA.symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ g) fA.w))
    have heC : fC.left ≫ (Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R C b K hK).left =
        (Relative.AffinePoints.relativeAffineScheme R B).hom ≫ g :=
      (congrArg (fun k => fC.left ≫ k) hC.symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ g) fC.w))
    exact heA.trans heC.symm
  change (algSpec R).map (CommAlgCat.ofHom φ).op ≫ Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A a Q hQ =
    (algSpec R).map (CommAlgCat.ofHom ψ).op ≫ Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R C b K hK at he
  rw [Affine.MatrixClassifyingEquations.Grassmannian.affineNormalizedClassifyingMap_comp_algebraMap, Affine.MatrixClassifyingEquations.Grassmannian.affineNormalizedClassifyingMap_comp_algebraMap] at he
  exact (Affine.MatrixClassifyingEquations.Grassmannian.affineNormalizedClassifyingMap_eq_iff_kernel R B a b (Q.map φ.toRingHom) (K.map ψ.toRingHom)
    (hQ.map φ.toRingHom) (hK.map ψ.toRingHom)).mp he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.MatrixOverlap
