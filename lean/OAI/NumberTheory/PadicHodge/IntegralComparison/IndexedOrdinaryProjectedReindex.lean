import OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ReindexComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Indexed Ordinary Projected Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryProjectedReindex.Ordinary

noncomputable section

/-! Projected refinement preserves the original ordinary
complex isomorphism before the final product comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u c d v t
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {C : Type c} [Category.{v} C] [HasBinaryProducts C]
  {D : Type d} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (F : C ⥤ D) (G : D ⥤ X.left.Opens) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor ((F.obj ∘ U) ∘ t)) G]
  [∀ (n : ℕ) (t : Fin (n + 1) → κ), PreservesLimit (Discrete.functor (V ∘ t)) G]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) (F ⋙ G)]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)

local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (ComplexShape.up ℕ) (OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryCech.Ordinary.diagram R X G )
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X

theorem bicomplex : GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K ≫
    ((NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).map
      (IndexedOrdinaryCech.Ordinary.complexIso R X (F ⋙ G) ).hom =
    (IndexedOrdinaryCech.Ordinary.bicomplexIso R X G V ).hom ≫
      GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap (F ⋙ G) U (G.obj ∘ V)
        (GeometricComparison.NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G (F.obj ∘ U) V r) Q := by
  let T := (NonemptyCechNerve.complexFunctor (A := ModuleCat.{u} R) U).mapHomologicalComplex (.up ℕ)
  let a := ((NonemptyCechNerve.complexFunctor (A := ModuleCat.{u} R) V).mapHomologicalComplex (.up ℕ)).map
    (IndexedOrdinaryCech.Ordinary.complexIso R X G ).hom
  have h₁ := (congrArg (fun b => GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K ≫ T.map b)
    (IndexedOrdinaryReindex.Ordinary.complex_hom R X F G ).symm).trans
      (GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplex_naturality F U V r
        (IndexedOrdinaryCech.Ordinary.complexIso R X G ).hom).symm
  exact h₁.trans ((congrArg (fun b => a ≫ b)
    (GeometricComparison.CechPresheaf.ReindexComposition.CechPresheafReindexComposition.bicomplex F G U V r Q)).trans (Category.assoc _ _ _).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryProjectedReindex.Ordinary
