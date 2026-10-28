import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PointedMapFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMultiplicationUnit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.SchemeProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.PointedMorphisms

/-! # Pointed Maps Are Homomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PointedMapsAreHomomorphisms

noncomputable section

/-! Over locally noetherian bases, every identity-preserving map between projectively presented abelian schemes is a group homomorphism, including over nonreduced bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem projectivePointedMap_isMonHom
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g h : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (PA : ProjectivePresentations.ProjectivePresentation A.scheme) (PB : ProjectivePresentations.ProjectivePresentation B.scheme)
    (f : A.scheme ⟶ B.scheme) (hf : η[A.scheme] ≫ f = η[B.scheme]) : IsMonHom f := by
  refine ⟨hf, ?_⟩
  obtain ⟨h₁, h₂⟩ := PointedMultiplicationUnit.pointedMultiplicationComposites_preserve_unit f hf
  let Q := (PA.product PA).product PB
  refine @Embedded.PointedMapFieldDetection.embeddedPointedMap_eq_of_fieldPullbacks S _ _ _ _ (A.product A) B Q.embedding Q.closedImmersion
    (μ[A.scheme] ≫ f) ((f ⊗ₘ f) ≫ μ[B.scheme]) h₁ h₂ ?_
  intro K _ s
  have hs : η[(A.pullback s).scheme] ≫ (Over.pullback s).map f = η[(B.pullback s).scheme] :=
    (MappedMonoidHomEquations.mappedMonoidHom_one_iff (Over.pullback s) f).mpr (congrArg (Over.pullback s).map hf)
  have hm : IsMonHom ((Over.pullback s).map f) :=
    Smooth.PointedMorphisms.abelianPointedMorphism_isMonHom (A.pullback s) (B.pullback s) ((Over.pullback s).map f) hs
  exact (MappedMonoidHomEquations.mappedMonoidHom_mul_iff (Over.pullback s) f).mp hm.mul_hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PointedMapsAreHomomorphisms
