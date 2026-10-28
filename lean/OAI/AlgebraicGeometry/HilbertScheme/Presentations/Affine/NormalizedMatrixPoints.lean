import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ChartClassifyingMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

/-! # Normalized Matrix Points -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedMatrixPoints.Grassmannian

noncomputable section

/-! Normalized matrices over any coefficient algebra give natural Grassmannian points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (R : CommRingCat.{u}) (A : Type u) [CommRing A] [Algebra R A]
variable (a : ι → ν) (Q : Matrix ι ν A) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q)

def affineNormalizedPointMatrix {T : Over (Spec R)} (f : T ⟶ Relative.AffinePoints.relativeAffineScheme R A) :
    Matrix ι ν Γ(T.left, ⊤) := Q.map (Relative.AffinePoints.relativeAffinePointEquiv R A T f).toRingHom

omit [Fintype ι] in
include hQ in
theorem affineNormalizedPointMatrix_normalized {T : Over (Spec R)}
    (f : T ⟶ Relative.AffinePoints.relativeAffineScheme R A) : Normalized.Matrices.Grassmannian.IsNormalized a (affineNormalizedPointMatrix R A Q f) :=
  hQ.map (Relative.AffinePoints.relativeAffinePointEquiv R A T f).toRingHom

omit [Fintype ι] [DecidableEq ι] in
theorem affineNormalizedPointMatrix_comp {T U : Over (Spec R)}
    (f : T ⟶ U) (g : U ⟶ Relative.AffinePoints.relativeAffineScheme R A) :
    affineNormalizedPointMatrix R A Q (f ≫ g) =
      (affineNormalizedPointMatrix R A Q g).map f.left.appTop.hom :=
  congrArg (fun φ : A →ₐ[R] Relative.AffinePoints.relativeGlobalAlgebra R T => Q.map φ.toRingHom)
    (Relative.AffinePoints.relativeAffinePointEquiv_natural R A f g)

def affineNormalizedClassifyingMap : Relative.AffinePoints.relativeAffineScheme R A ⟶
    Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := ν) (Spec R) :=
  Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap a (affineNormalizedPointMatrix R A Q (𝟙 _))
    (affineNormalizedPointMatrix_normalized R A a Q hQ (𝟙 _))

theorem affineNormalizedClassifyingMap_comp {T : Over (Spec R)} (f : T ⟶ Relative.AffinePoints.relativeAffineScheme R A) :
    f ≫ affineNormalizedClassifyingMap R A a Q hQ =
      Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap a (affineNormalizedPointMatrix R A Q f)
        (affineNormalizedPointMatrix_normalized R A a Q hQ f) := by
  rw [affineNormalizedClassifyingMap, ← Quotient.ChartClassifyingMap.Grassmannian.normalizedMatrixClassifyingMap_natural]
  have hm := affineNormalizedPointMatrix_comp R A Q f (𝟙 _)
  rw [Category.comp_id] at hm
  congr 1

variable [Fintype ν] [DecidableEq ν]

include hQ in
theorem affineNormalizedPointMatrix_kernel {T : Over (Spec R)} (f : T ⟶ Relative.AffinePoints.relativeAffineScheme R A)
    (N : Submodule R (ν → R))
    (hN : (Matrix.toLin' Q).ker = Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R A) N) :
    (Matrix.toLin' (affineNormalizedPointMatrix R A Q f)).ker =
      Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R (Relative.AffinePoints.relativeGlobalAlgebra R T)) N := by
  let φ := Relative.AffinePoints.relativeAffinePointEquiv R A T f
  change (Matrix.toLin' (Q.map φ.toRingHom)).ker = _
  rw [← Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange φ.toRingHom a Q hQ, hN, ← Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_comp]
  have hc : φ.toRingHom.comp (algebraMap R A) = algebraMap R (Relative.AffinePoints.relativeGlobalAlgebra R T) := by
    ext r
    exact φ.commutes r
  exact congrArg (fun α => Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension α N) hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedMatrixPoints.Grassmannian
