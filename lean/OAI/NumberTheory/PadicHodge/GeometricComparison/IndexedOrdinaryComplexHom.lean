import OAI.NumberTheory.PadicHodge.GeometricComparison.IndexedOrdinaryCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ReindexProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Indexed Ordinary Complex Hom -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IndexedOrdinaryComplexHom.IndexedOrdinaryQuotientReindex

noncomputable section

/-! The original ordinary quotient comparison preserves projected
cover refinement when affine indexing is changed to actual opens. -/

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

omit [HasBinaryProducts C] [Quiver.IsThin D] [HasBinaryProducts D] in
theorem complex_hom : ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{0} R) F).mapHomologicalComplex (.up ℕ)).map
    (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.complexIso R X G I).hom =
      (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.complexIso R X (F ⋙ G) I).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext W
  rfl

theorem bicomplex : CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K ≫
    (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.bicomplexIso R X (F ⋙ G) U I).hom =
      (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.bicomplexIso R X G V I).hom ≫
        CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.bicomplexMap (G.obj ∘ V) (G.obj ∘ F.obj ∘ U)
          (NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G (F.obj ∘ U) V r) Q := by
  let T := (IntegralComparison.NonemptyCechNerve.complexFunctor (A := ModuleCat.{0} R) U).mapHomologicalComplex (.up ℕ)
  have h₁ := (congrArg (fun a => CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K ≫ T.map a)
    (complex_hom R X F G I).symm).trans
      (CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.bicomplex_naturality F U V r (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.complexIso R X G I).hom).symm
  have h₂ := CechPresheaf.ReindexProduct.CechPresheafReindexProduct.bicomplex F G U V r Q
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

theorem total : CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r K ≫
    (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.totalIso R X (F ⋙ G) U I).hom =
      (IndexedOrdinaryCech.IndexedOrdinaryQuotientCech.totalIso R X G V I).hom ≫
        CechPresheaf.RefinementCoefficient.CechPresheafRefinementCoefficient.map (G.obj ∘ V) (G.obj ∘ F.obj ∘ U)
          (NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G (F.obj ∘ U) V r) Q :=
  (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)).symm.trans
    ((congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ)) (bicomplex R X F G U V I r)).trans
      (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IndexedOrdinaryComplexHom.IndexedOrdinaryQuotientReindex
