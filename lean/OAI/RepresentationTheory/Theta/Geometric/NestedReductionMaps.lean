import OAI.RepresentationTheory.Theta.Geometric.Affine.TestMaps
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Nested Reduction Maps -/

namespace OAI.RepresentationTheory.Theta.Geometric.NestedReductionMaps

noncomputable section

/-! The native maps of successive quotient tests factor through the
single quotient by the larger ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def complexReductionMap {R : Type} [CommRing R] [Algebra ℂ R] (I : Ideal R) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (R ⧸ I) ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (R ⧸ I) (Ideal.Quotient.mkₐ ℂ I)

set_option backward.isDefEq.respectTransparency false in
theorem complexReductionMap_nested_factor {R : Type} [CommRing R] [Algebra ℂ R]
    (I J : Ideal R) (hIJ : I ≤ J) :
    ∃ w : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (R ⧸ J),
      complexReductionMap (J.map (Ideal.Quotient.mk I)) ≫ complexReductionMap I =
        w ≫ complexReductionMap J := by
  let e := DoubleQuot.quotQuotEquivQuotOfLEₐ ℂ hIJ
  refine ⟨AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (R ⧸ J) ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) e.symm.toAlgHom, ?_⟩
  unfold complexReductionMap
  rw [← Affine.TestMaps.affineAlgHomOverSpecEquiv_comp, ← Affine.TestMaps.affineAlgHomOverSpecEquiv_comp]
  apply congrArg (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)))
  exact (DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mkₐ ℂ hIJ).symm

end

end OAI.RepresentationTheory.Theta.Geometric.NestedReductionMaps
