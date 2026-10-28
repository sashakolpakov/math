import OAI.RepresentationTheory.Theta.Geometric.RigidifiedFiniteLineDescent
import OAI.RepresentationTheory.Theta.Geometric.Finite.MultiplicativeFamilyDescent
import OAI.RepresentationTheory.Theta.Geometric.HomogeneousUniversalTensor
import OAI.RepresentationTheory.Theta.Geometric.RigidifiedParameterPullback
import OAI.RepresentationTheory.Theta.Geometric.AbelianScheme

/-! # Homogeneous Family Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.HomogeneousFamilyDescent

noncomputable section

/-! A homogeneous rigidified family over an arbitrary complex algebra
descends to a finite-type affine test with both properties retained. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem exists_finiteType_homogeneous_family
    {R : Type} [CommRing R] [Algebra ℂ R] (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    [QuasiCompact A.toOver.hom] [QuasiSeparated A.toOver.hom]
    (L : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R))
    (hL : (AbelianScheme.abelianSchemeOfVariety A).IsHomogeneousPicardClass (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle)) :
    ∃ T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, IsAffine T.left ∧ LocallyOfFiniteType T.hom ∧
      ∃ (j : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ T) (N : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver T),
        (AbelianScheme.abelianSchemeOfVariety A).IsHomogeneousPicardClass T (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N.bundle) ∧
        Nonempty ((N.bundle.pullback (j ▷ A.toOver).left).sheaf ≅ L.bundle.sheaf) := by
  let : CompactSpace (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left := inferInstanceAs (CompactSpace (Spec (.of R)))
  let : QuasiSeparatedSpace (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of R)))
  obtain ⟨S, hS, NS, eS⟩ := RigidifiedFiniteLineDescent.exists_fg_rigidified_abelian_family_line A L
  let : Algebra.FiniteType ℂ S := (Subalgebra.fg_iff_finiteType S).mp hS
  have hSclass : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf
      (NS.bundle.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap S R ▷ A.toOver).left) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle := Quotient.sound eS
  have hR : MultiplicativeFamilyCriterion.IsMultiplicativeFamilyClass (AbelianScheme.abelianSchemeOfVariety A) (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (NS.bundle.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap S R ▷ A.toOver).left)) := by
    rw [hSclass]
    exact HomogeneousUniversalTensor.multiplicative_family_of_homogeneous (AbelianScheme.abelianSchemeOfVariety A) _ hL
      (Quotient.sound ⟨L.axis⟩)
  obtain ⟨U, hU, hm⟩ := MultiplicativeFamilyDescent.exists_fg_multiplicative_family_extension (AbelianScheme.abelianSchemeOfVariety A) NS.bundle hR
  let : Algebra.FiniteType S U := (Subalgebra.fg_iff_finiteType U).mp hU
  let : Algebra.FiniteType ℂ U := Algebra.FiniteType.trans (R := ℂ) (S := S) (A := U)
    (inferInstanceAs (Algebra.FiniteType ℂ S)) (inferInstanceAs (Algebra.FiniteType S U))
  let T := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ U
  let p := Complex.AlgebraParameterMap.complexAlgebraParameterMap S U
  let j := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ U R (U.val.restrictScalars ℂ)
  let N := RigidifiedParameterPullback.rigidifiedParameterPullback NS p
  have hj : j ≫ p = Complex.AlgebraParameterMap.complexAlgebraParameterMap S R :=
    Complex.AlgebraParameterMap.complexAlgebraParameterMap_subalgebra_factor S R U
  have hfin : LocallyOfFiniteType T.hom := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ U)))
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap ℂ U))).mpr
        (RingHom.finiteType_algebraMap.mpr inferInstance)
  refine ⟨T, inferInstanceAs (IsAffine (Spec (.of U))), hfin, j, N, ?_, ?_⟩
  · apply MultiplicativeFamilyCriterion.homogeneous_of_multiplicative_family
    change MultiplicativeFamilyCriterion.IsMultiplicativeFamilyClass (AbelianScheme.abelianSchemeOfVariety A) T
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (NS.bundle.pullback (p ⊗ₘ 𝟙 A.toOver).left))
    rw [tensorHom_id]
    exact hm
  · have h := NS.line_class_pullback j p
    rw [hj] at h
    have ht : (Complex.AlgebraParameterMap.complexAlgebraParameterMap S R ⊗ₘ 𝟙 A.toOver) =
        Complex.AlgebraParameterMap.complexAlgebraParameterMap S R ▷ A.toOver := tensorHom_id _ _
    change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((NS.line p).pullback (j ⊗ₘ 𝟙 A.toOver).left) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (NS.bundle.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap S R ⊗ₘ 𝟙 A.toOver).left) at h
    rw [tensorHom_id, ht] at h
    exact Quotient.exact (h.trans hSclass)

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.HomogeneousFamilyDescent
