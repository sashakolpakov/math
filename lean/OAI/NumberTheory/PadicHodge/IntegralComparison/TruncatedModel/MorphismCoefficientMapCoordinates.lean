import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoefficientMapData

/-! # Morphism Coefficient Map Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoefficientMapCoordinates

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem replace_last {C : Type*} [Category C] {A B D E : C}
    {a : A ⟶ B} {b : B ⟶ E} {c : A ⟶ D} {d d' : D ⟶ E}
    (h : a ≫ b = c ≫ d) (hd : d = d') : a ≫ b = c ≫ d' :=
  h.trans (congrArg (fun m => c ≫ m) hd)

section
universe ru rv cu cv
variable (R : Type ru) [CommRing R] {C : Type cu} [Category.{cv} C]
  (E : SimplicialObject (CategoryTheory.Limits.FormalCoproduct.{0} C))
local instance original_limits : CategoryTheory.Limits.HasLimitsOfSize.{0,0}
    (ModuleCat.{max ru rv} R) := ModuleCat.hasLimitsOfSize.{0,0,max ru rv,ru}
local instance original_colimits : CategoryTheory.Limits.HasColimitsOfSize.{0,0}
    (ModuleCat.{max ru rv} R) := ModuleCat.hasColimitsOfSize.{max ru rv,ru,0,0} R

private theorem original_map_of_eq
    {P Q : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{max ru rv} R) ℕ}
    (f : P ⟶ Q)
    (a : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) Q)
    (ha : a = AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) f) :
    (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map f = AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R E a := by
  subst a
  exact Cech.AssemblyTotalMap.map.{ru,rv,cu,cv} R E f
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

abbrev geometric_original := original_map_of_eq.{1,2,0,0}
  (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
  (NonemptyCechNerve.nerve (MorphismCover.pairs p k n u))
  (P := ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op ⋙
    PrincipalComplex.Comparison.pdComplexes p k n X₂ Y₂ f₂ hp₂) ⋙
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ))
  (Q := ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙
    PrincipalComplex.Comparison.pdComplexes p k n X₁ Y₁ f₁ hp₁) ⋙
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ))
  (Functor.whiskerRight
    (MorphismPrincipal.Comparison.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq)
    ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ)))
  (MorphismFrameDiagonal.map p k n u v f₁ f₂ hp₁ hp₂ sq)
  (MorphismCoefficientMapData.Coordinates.diagonal_map p k n u v f₁ f₂ hp₁ hp₂ sq)

abbrev ordinary_natural := replace_last
  (MorphismCoefficientCech.ordinary_natural p k n u v f₁ f₂ hp₁ hp₂ sq)
  (geometric_original p k n u v f₁ f₂ hp₁ hp₂ sq)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoefficientMapCoordinates
