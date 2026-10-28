import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedMatrixPoints

/-! # Matrix Classifying Equations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.MatrixClassifyingEquations.Grassmannian

noncomputable section

/-! Algebraic formulas for equality and restriction of affine matrix classifying maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable (R : CommRingCat.{u}) (A : Type u) [CommRing A] [Algebra R A]

theorem affineNormalizedClassifyingMap_eq_iff_kernel
    (a b : ι → ν) (Q K : Matrix ι ν A) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) (hK : Normalized.Matrices.Grassmannian.IsNormalized b K) :
    NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A a Q hQ = NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A b K hK ↔
      (Matrix.toLin' Q).ker = (Matrix.toLin' K).ker := by
  let e := Relative.AffinePoints.relativeAffineGlobalEquiv R A
  let ψ : A →+* Γ((Relative.AffinePoints.relativeAffineScheme R A).left, ⊤) := e.toRingHom
  change Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap (T := Relative.AffinePoints.relativeAffineScheme R A) a
      (Q.map ψ) (hQ.map ψ) =
    Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap (T := Relative.AffinePoints.relativeAffineScheme R A) b
      (K.map ψ) (hK.map ψ) ↔ _
  rw [Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap_eq_iff,
    ← Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange ψ a Q hQ, ← Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange ψ b K hK]
  exact ⟨fun h => Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_injective e.toRingEquiv h,
    fun h => congrArg (Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension ψ) h⟩

theorem affineNormalizedClassifyingMap_comp_algebraMap
    {B : Type u} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (a : ι → ν) (Q : Matrix ι ν A) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    (algSpec R).map (CommAlgCat.ofHom φ).op ≫ NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A a Q hQ =
      NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R B a (Q.map φ.toRingHom) (hQ.map φ.toRingHom) := by
  let f : Relative.AffinePoints.relativeAffineScheme R B ⟶ Relative.AffinePoints.relativeAffineScheme R A :=
    (algSpec R).map (CommAlgCat.ofHom φ).op
  have hφ := Relative.AffinePoints.relativeAffinePointEquiv_postcomp R A φ (𝟙 (Relative.AffinePoints.relativeAffineScheme R B))
  change Relative.AffinePoints.relativeAffinePointEquiv R A (Relative.AffinePoints.relativeAffineScheme R B) (𝟙 _ ≫ f) =
    (Relative.AffinePoints.relativeAffinePointEquiv R B (Relative.AffinePoints.relativeAffineScheme R B) (𝟙 _)).comp φ at hφ
  rw [Category.id_comp] at hφ
  have hm : NormalizedMatrixPoints.Grassmannian.affineNormalizedPointMatrix R A Q f =
      NormalizedMatrixPoints.Grassmannian.affineNormalizedPointMatrix R B (Q.map φ.toRingHom) (𝟙 _) :=
    congrArg (fun ψ : A →ₐ[R] Relative.AffinePoints.relativeGlobalAlgebra R (Relative.AffinePoints.relativeAffineScheme R B) => Q.map ψ.toRingHom) hφ
  change f ≫ NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A a Q hQ = _
  rw [NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap_comp]
  change Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap a (NormalizedMatrixPoints.Grassmannian.affineNormalizedPointMatrix R A Q f) _ =
    Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap a (NormalizedMatrixPoints.Grassmannian.affineNormalizedPointMatrix R B (Q.map φ.toRingHom) (𝟙 _)) _
  apply (Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap_eq_iff _ _ _ _ _ _).mpr
  exact congrArg (fun L : Matrix ι ν Γ((Relative.AffinePoints.relativeAffineScheme R B).left, ⊤) => (Matrix.toLin' L).ker) hm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.MatrixClassifyingEquations.Grassmannian
