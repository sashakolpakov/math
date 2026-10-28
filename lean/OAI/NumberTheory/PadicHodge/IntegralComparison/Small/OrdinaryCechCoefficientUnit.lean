import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjection
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ProductCoefficient

/-! # Ordinary Cech Coefficient Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechCoefficientUnit.Ordinary

noncomputable section

/-! The original small-cover ordinary coordinates followed by the
actual sheaf unit give the canonical coefficient comparison on the
native sheafified de Rham total. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uD vD
variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

local instance tuple_preserves (m : ℕ) (t : Fin (m+1) → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index R X) :
    PreservesLimit (Discrete.functor (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X ∘ t))
      (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.inclusion_preserves X.left _

variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]

def affineTotal : CochainComplex (X.left.affineOpensᵒᵖ ⥤ D) ℕ ⥤ CochainComplex D ℕ :=
  (NonemptyCechNerve.complexFunctor (A := D) (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X)).mapHomologicalComplex
    (.up ℕ) ⋙ HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)

def productIso (K : CochainComplex (X.left.Opensᵒᵖ ⥤ D) ℕ) :=
  HomologicalComplex₂.total.mapIso
    (GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X) K) (.up ℕ)

theorem product_naturality {K L : CochainComplex (X.left.Opensᵒᵖ ⥤ D) ℕ} (a : K ⟶ L) :
    (affineTotal R X).map
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex
        (.up ℕ)).map a) ≫ (productIso R X L).hom =
    (productIso R X K).hom ≫
      (OrderedCech.TotalProjection.ordinary (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X)).map a := by
  let T := HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)
  have h := ((NatIso.mapHomologicalComplex
    (GeometricComparison.NonemptyCech.ProductBaseChangeNaturality.NonemptyCechProductBaseChangeNaturality.iso (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X)) (.up ℕ)).hom.naturality a)
  exact (T.map_comp _ _).symm.trans ((congrArg T.map h).trans (T.map_comp _ _))

def affineUnit : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (OrdinaryCechTotal.Ordinary.diagram R X) ⟶
    ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex
      (.up ℕ)).obj (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex R X) :=
  (OrdinaryCechTotal.Ordinary.complexIso R X).hom ≫
    ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex
      (.up ℕ)).map (IntrinsicDeRham.SectionUnit.Intrinsic.presheafUnit R X)

theorem original_factorization : (OrdinaryCechTotal.Ordinary.totalIso R X).hom =
    (affineTotal R X).map
      (OrdinaryCechTotal.Ordinary.complexIso R X).hom ≫
    (productIso R X (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)).hom ≫
    (OrderedCech.TotalProjection.ordinary (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X)).map
      (IntrinsicDeRham.SectionUnit.Intrinsic.presheafUnit R X) := by
  simp only [OrdinaryCechTotal.Ordinary.totalIso, OrdinaryCechTotal.Ordinary.bicomplexIso,
    Iso.trans_hom, HomologicalComplex₂.total.mapIso_hom, HomologicalComplex₂.total.map_comp,
    Functor.mapIso_hom, Category.assoc]
  rfl

variable (F : ModuleCat R ⥤ D) [F.Additive]

def sourceCoordinates := GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso F
  (NonemptyCechNerve.nerve (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X))
  (OrdinaryCechTotal.Ordinary.finiteIndices R X)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (OrdinaryCechTotal.Ordinary.diagram R X))

def targetCoordinates := GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso F
  (NonemptyCechNerve.nerve (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X))
  (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X))
  (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex R X)

def mappedUnit := ((GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.presheaves F).mapHomologicalComplex (.up ℕ)).map
  (affineUnit R X)

def targetProductIso := productIso R X
  (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex R X))

theorem comparison :
    (F.mapHomologicalComplex (.up ℕ)).map (OrdinaryCechTotal.Ordinary.totalIso R X).hom ≫
      (targetCoordinates R X F).hom =
    (sourceCoordinates R X F).hom ≫
      (affineTotal R X).map (mappedUnit R X F) ≫
        (targetProductIso R X F).hom := by
  let N := NonemptyCechNerve.nerve (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X)
  let V := NonemptyCechNerve.nerve (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X)
  let hN := OrdinaryCechTotal.Ordinary.finiteIndices R X
  let hV := GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X)
  let a := (OrdinaryCechTotal.Ordinary.complexIso R X).hom
  let b := IntrinsicDeRham.SectionUnit.Intrinsic.presheafUnit R X
  let FP := (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.presheaves (C := X.left.Opens) F).mapHomologicalComplex (.up ℕ)
  have ha := GeometricComparison.CechPresheaf.CoefficientNaturality.CechPresheafCoefficientNaturality.total F N hN a
  have hp := GeometricComparison.CechPresheaf.ProductCoefficient.CechPresheafProductCoefficient.total (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) F
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
  have hb := GeometricComparison.CechPresheaf.CoefficientNaturality.CechPresheafCoefficientNaturality.total F V hV b
  have hn := product_naturality R X
    (((GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.presheaves F).mapHomologicalComplex (.up ℕ)).map b)
  rw [original_factorization, Functor.map_comp, Functor.map_comp]
  dsimp only [targetCoordinates, sourceCoordinates, mappedUnit, affineUnit, targetProductIso]
  simp only [Category.assoc]
  erw [hb]
  erw [← Category.assoc _ _ (GeometricComparison.CechPresheaf.CoefficientNaturality.CechPresheafCoefficientNaturality.totalMap V (FP.map b)), hp]
  simp only [Category.assoc]
  erw [← Category.assoc, ha]
  simp only [Category.assoc]
  erw [hn.symm]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechCoefficientUnit.Ordinary
