import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafSourceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelResolutionGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Intrinsic

/-! # Sheaf Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafProduct.OrderedComparison

noncomputable section

section

/-! Product coordinates for the actual sheaf comparison, with the
naturality square proved before specializing the resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem product_square
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
    (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
    [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
    (K L : CochainComplex (X.left.Opensᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (N : CochainComplex (X.left.affineOpensᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (e : N ≅ ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
      (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).obj L)
    (a : K ⟶ L)
    (b : ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
      (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).obj K ⟶ N)
    (hb : b ≫ e.hom = ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
      (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).map a) :
    (OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X).map b ≫
      (IntrinsicConeCoordinates.Intrinsic.productIso p k n X L N e).hom =
    (Small.OrdinaryCechCoefficientUnit.Ordinary.productIso (Truncated.Witt.Ring p k n) X K).hom ≫
      (OrderedCech.TotalProjection.ordinary
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)).map a := by
  change (Small.OrdinaryCechCoefficientUnit.Ordinary.affineTotal
      (Truncated.Witt.Ring p k n) X).map b ≫
    ((Small.OrdinaryCechCoefficientUnit.Ordinary.affineTotal
      (Truncated.Witt.Ring p k n) X).map e.hom ≫
      (Small.OrdinaryCechCoefficientUnit.Ordinary.productIso
        (Truncated.Witt.Ring p k n) X L).hom) = _
  rw [← Category.assoc, ← Functor.map_comp, hb]
  exact Small.OrdinaryCechCoefficientUnit.Ordinary.product_naturality
    (Truncated.Witt.Ring p k n) X a

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev source := ((sheafToPresheaf (Opens.grothendieckTopology X.left)
    (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))).mapHomologicalComplex
      (.up ℕ)).obj (ModelSheafComparison.source p k n X)

abbrev target := CechIso.ResolutionGlobal.presheaf p k n X Y f I

def map : source p k n X ⟶ target p k n X Y f I :=
  ((sheafToPresheaf (Opens.grothendieckTopology X.left)
    (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))).mapHomologicalComplex
      (.up ℕ)).map (ModelSheafComparison.map p k n X Y f hp I)

def ordinaryMap := (OrderedCech.TotalProjection.ordinary
  (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)).map (OrderedComparison.map p k n X Y f hp I)

def orderedMap := (OrderedCech.TotalProjection.ordered
  (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)).map (OrderedComparison.map p k n X Y f hp I)

theorem affine_coordinate :
    SheafGlobalData.Comparison.affineMap p k n X Y f hp I ≫
      (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I).hom =
    ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
      (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).map
        (OrderedComparison.map p k n X Y f hp I) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

section

/-! Naturality of the actual product comparison, with all map carriers
inherited from the checked generic square. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev product_naturality :=
  product_square p k n X (source p k n X) (target p k n X Y f I)
    (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
    (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I)
    (OrderedComparison.map p k n X Y f hp I)
    (SheafGlobalData.Comparison.affineMap p k n X Y f hp I)
    (affine_coordinate p k n X Y f hp I)

end

/-! The ordinary sheaf comparison square, composed with the original
source coordinates before specializing the resolution complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem source_paste {C : Type*} [Category C] {A B D E F G : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E} {u : E ⟶ G}
    {v : D ⟶ F} {w : F ⟶ G} {d : A ⟶ E}
    (h : a ≫ b ≫ c = d) (k : v ≫ w = c ≫ u) :
    d ≫ u = a ≫ b ≫ v ≫ w := by
  rw [← h]
  simp only [Category.assoc]
  rw [← k]

theorem source_chain
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
    (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
    [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
    (L : CochainComplex (X.left.Opensᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (N : CochainComplex (X.left.affineOpensᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (e : N ≅ ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
      (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).obj L)
    (a : source p k n X ⟶ L)
    (b : ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
      (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).obj
        (source p k n X) ⟶ N)
    (hb : b ≫ e.hom = ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
      (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).map a) :
    (SheafSourceCoordinates.nativeCoordinates p k n X).hom ≫
      (OrderedCech.TotalProjection.ordinary
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)).map a =
    (OrdinaryGlobal.OrdinaryComparison.coordinates p k n X).hom ≫
      SheafGlobalData.Comparison.totalUnit p k n X ≫
        (OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X).map b ≫
          (IntrinsicConeCoordinates.Intrinsic.productIso p k n X L N e).hom :=
  source_paste (SheafSourceCoordinates.comparison p k n X)
    (product_square p k n X (source p k n X) L N e a b hb)

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev chain_comparison :=
  source_chain p k n X (target p k n X Y f I)
    (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
    (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I)
    (OrderedComparison.map p k n X Y f hp I)
    (SheafGlobalData.Comparison.affineMap p k n X Y f hp I)
    (affine_coordinate p k n X Y f hp I)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafProduct.OrderedComparison
