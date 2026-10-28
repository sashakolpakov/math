import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicHomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined

/-! # Morphism Common Iso Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonIsoCoordinates

noncomputable section

/-! The native common-cover coefficient isomorphism, with its original
presheaf-total target fixed before applying homology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {Y₁ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom]
  (f₁ : Y₁.left ⟶ X₁.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

def source : CochainComplex (ModuleCat (WittVector p k)) ℕ :=
  GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total
    (NonemptyCechNerve.nerve (MorphismCover.pairs p k n u))
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙ OrdinaryBaseIso.Ordinary.target p k n X₁)

def target : CochainComplex
    (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (MorphismCover.pairs p k n u)
    (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
          (FrameDiagonalMap.source p k n X₁ Y₁ f₁ hp₁)))

def iso :
    ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ)).obj
      (source p k n u) ≅ target p k n u f₁ hp₁ :=
  MorphismCoefficientCech.ordinarySourceIso p k n u f₁ hp₁

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

def homologyIso (q : ℕ) := GeometricComparison.ExactHomology.ExactHomologyComparison.iso
  (SmoothWitt.DeRham.Comparison.coefficientFunctor p k) (.up ℕ)
  (source p k n u) (target p k n u f₁ hp₁) (iso p k n u f₁ hp₁) q

omit [IsSeparated Y₁.hom] in
theorem comparison (q : ℕ) :
    (MorphismIntrinsicHomology.Intrinsic.commonSourceIso p k n u f₁ hp₁ q).hom =
      (homologyIso p k n u f₁ hp₁ q).hom := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonIsoCoordinates
