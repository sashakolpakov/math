import OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ReindexProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Indexed Ordinary Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryReindex.Ordinary

noncomputable section

/-! The original ordinary comparison preserves projected
cover refinement when affine indexing is changed to actual opens. -/

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

omit [HasBinaryProducts C] [Quiver.IsThin D] [HasBinaryProducts D] in
theorem complex_hom : ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u} R) F).mapHomologicalComplex (.up ℕ)).map
    (IndexedOrdinaryCech.Ordinary.complexIso R X G ).hom =
      (IndexedOrdinaryCech.Ordinary.complexIso R X (F ⋙ G) ).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext W
  rfl

theorem bicomplex : GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K ≫
    (IndexedOrdinaryCech.Ordinary.bicomplexIso R X (F ⋙ G) U ).hom =
      (IndexedOrdinaryCech.Ordinary.bicomplexIso R X G V ).hom ≫
        GeometricComparison.CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.bicomplexMap (G.obj ∘ V) (G.obj ∘ F.obj ∘ U)
          (GeometricComparison.NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G (F.obj ∘ U) V r) Q := by
  let T := (NonemptyCechNerve.complexFunctor (A := ModuleCat.{u} R) U).mapHomologicalComplex (.up ℕ)
  have h₁ := (congrArg (fun a => GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K ≫ T.map a)
    (complex_hom R X F G ).symm).trans
      (GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplex_naturality F U V r (IndexedOrdinaryCech.Ordinary.complexIso R X G ).hom).symm
  have h₂ := GeometricComparison.CechPresheaf.ReindexProduct.CechPresheafReindexProduct.bicomplex F G U V r Q
  exact GeometricComparison.ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

theorem total : GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r K ≫
    (IndexedOrdinaryCech.Ordinary.totalIso R X (F ⋙ G) U ).hom =
      (IndexedOrdinaryCech.Ordinary.totalIso R X G V ).hom ≫
        GeometricComparison.CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.map (G.obj ∘ V) (G.obj ∘ F.obj ∘ U)
          (GeometricComparison.NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G (F.obj ∘ U) V r) Q :=
  (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)).symm.trans
    ((congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ)) (bicomplex R X F G U V  r)).trans
      (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryReindex.Ordinary
