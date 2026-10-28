import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.AssemblyTotalMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoefficientCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameDiagonal

/-! # Morphism Coefficient Map Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoefficientMapData.Coordinates

noncomputable section

/-! The actual coefficient-level geometric map is the original
presheaf-total map, with the pulled-back source complex kept explicit. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe ru rv cu cv du dv
variable (R : Type ru) [CommRing R] {C : Type cu} [Category.{cv} C]
  (E : SimplicialObject (CategoryTheory.Limits.FormalCoproduct.{0} C))
  {D : Type du} [Category.{dv} D] (r : C ⥤ D)

local instance generic_limits : CategoryTheory.Limits.HasLimitsOfSize.{0,0}
    (ModuleCat.{max ru rv} R) := ModuleCat.hasLimitsOfSize.{0,0,max ru rv,ru}
local instance generic_colimits : CategoryTheory.Limits.HasColimitsOfSize.{0,0}
    (ModuleCat.{max ru rv} R) := ModuleCat.hasColimitsOfSize.{max ru rv,ru,0,0} R

private theorem assembly_of_eq
    {P : Dᵒᵖ ⥤ CochainComplex (ModuleCat.{max ru rv} R) ℕ}
    {Q : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{max ru rv} R) ℕ}
    (f : r.op ⋙ P ⟶ Q)
    (a : ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback R r).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P) ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) Q)
    (ha : a = AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) f) :
    (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map f = AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R E a := by
  subst a
  exact Cech.AssemblyTotalMap.refined_map.{ru,rv,cu,cv,du,dv} R E r f
end

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

omit [IsProper X₁.hom] [IsProper X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem diagonal_map :
    MorphismFrameDiagonal.map p k n u v f₁ f₂ hp₁ hp₂ sq =
      AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ)
        (Functor.whiskerRight
          (MorphismPrincipal.Comparison.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq)
          ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ))) := rfl

abbrev geometric_map := assembly_of_eq.{1,2,0,0,0,0}
  (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
  (NonemptyCechNerve.nerve (MorphismCover.pairs p k n u))
  (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)
  (P := FrameDiagonalMap.source p k n X₂ Y₂ f₂ hp₂)
  (Q := (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙
    FrameDiagonalMap.source p k n X₁ Y₁ f₁ hp₁)
  (Functor.whiskerRight
    (MorphismPrincipal.Comparison.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq)
    ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ)))
  (MorphismFrameDiagonal.map p k n u v f₁ f₂ hp₁ hp₂ sq)
  (diagonal_map p k n u v f₁ f₂ hp₁ hp₂ sq)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoefficientMapData.Coordinates
