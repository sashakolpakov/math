import OAI.NumberTheory.PadicHodge.GeometricComparison.IndexedOrdinaryComplexHom
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ReindexComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Ordinary Quotient Projected Reindex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryQuotientProjectedReindex.IndexedOrdinaryQuotientProjectedReindex

noncomputable section

/-! Projected refinement preserves the original ordinary quotient
complex isomorphism before the final product comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe v t
variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {C : Type} [Category.{v} C] [HasBinaryProducts C]
  {D : Type} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (F : C ⥤ D) (G : D ⥤ X.left.Opens) {ι κ : Type} (U : ι → C) (V : κ → D) (I : Ideal R)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor ((F.obj ∘ U) ∘ t)) G]
  [∀ (n : ℕ) (t : Fin (n + 1) → κ), PreservesLimit (Discrete.functor (V ∘ t)) G]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) (F ⋙ G)]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)

local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (ComplexShape.up ℕ) (OAI.NumberTheory.PadicHodge.GeometricComparison.IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.diagram R X G I)
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryAffineTotal.OrdinaryAffineQuotientCech.quotientComplex R X I

theorem bicomplex : CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K ≫
    ((IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).map
      (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.complexIso R X (F ⋙ G) I).hom =
    (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.bicomplexIso R X G V I).hom ≫
      CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap (F ⋙ G) U (G.obj ∘ V)
        (NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G (F.obj ∘ U) V r) Q := by
  let T := (IntegralComparison.NonemptyCechNerve.complexFunctor (A := ModuleCat.{0} R) U).mapHomologicalComplex (.up ℕ)
  let a := ((IntegralComparison.NonemptyCechNerve.complexFunctor (A := ModuleCat.{0} R) V).mapHomologicalComplex (.up ℕ)).map
    (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.complexIso R X G I).hom
  have h₁ := (congrArg (fun b => CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K ≫ T.map b)
    (IndexedOrdinaryComplexHom.IndexedOrdinaryQuotientReindex.complex_hom R X F G I).symm).trans
      (CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplex_naturality F U V r
        (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.complexIso R X G I).hom).symm
  exact h₁.trans ((congrArg (fun b => a ≫ b)
    (CechPresheaf.ReindexComposition.CechPresheafReindexComposition.bicomplex F G U V r Q)).trans (Category.assoc _ _ _).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryQuotientProjectedReindex.IndexedOrdinaryQuotientProjectedReindex
