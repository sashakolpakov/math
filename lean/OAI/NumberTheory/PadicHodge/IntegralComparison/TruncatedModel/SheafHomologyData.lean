import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafProduct

/-! # Sheaf Homology Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafHomologyData.OrderedComparison

noncomputable section

section

/-! Native ordinary total coordinates and the checked chain square,
transported to homology before specializing the resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Typed

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

def nativeCoordinates :
    GlobalDeRham.Comparison.complex p k n X ⟶
      IntrinsicConeCoordinates.Intrinsic.ordinaryTotal p k n X (SheafProduct.OrderedComparison.source p k n X) :=
  (SheafSourceCoordinates.nativeCoordinates p k n X).hom

def ordinaryMap
    {K L : CochainComplex (X.left.Opensᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
    (a : K ⟶ L) :
    IntrinsicConeCoordinates.Intrinsic.ordinaryTotal p k n X K ⟶
      IntrinsicConeCoordinates.Intrinsic.ordinaryTotal p k n X L :=
  (OrderedCech.TotalProjection.ordinary
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)).map a

variable
  (L : CochainComplex (X.left.Opensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
  (N : CochainComplex (X.left.affineOpensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
  (e : N ≅ ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
    (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).obj L)
  (a : SheafProduct.OrderedComparison.source p k n X ⟶ L)
  (b : ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
    (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).obj
      (SheafProduct.OrderedComparison.source p k n X) ⟶ N)
  (hb : b ≫ e.hom = ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
    (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).map a)

include hb in
theorem chain :
    nativeCoordinates p k n X ≫ ordinaryMap p k n X a =
    (OrdinaryGlobal.OrdinaryComparison.coordinates p k n X).hom ≫
      SheafGlobalData.Comparison.totalUnit p k n X ≫
        (OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X).map b ≫
          (IntrinsicConeCoordinates.Intrinsic.productIso p k n X L N e).hom :=
  SheafProduct.OrderedComparison.source_chain p k n X L N e a b hb

include hb in
theorem homology_chain (q : ℕ) :
    homologyMap (nativeCoordinates p k n X) q ≫
      homologyMap (ordinaryMap p k n X a) q =
    homologyMap (OrdinaryGlobal.OrdinaryComparison.coordinates p k n X).hom q ≫
      homologyMap (SheafGlobalData.Comparison.totalUnit p k n X) q ≫
        homologyMap ((OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X).map b) q ≫
          homologyMap (IntrinsicConeCoordinates.Intrinsic.productIso p k n X L N e).hom q := by
  have h := congrArg (fun t :
      GlobalDeRham.Comparison.complex p k n X ⟶
        IntrinsicConeCoordinates.Intrinsic.ordinaryTotal p k n X L =>
      homologyMap t q) (chain p k n X L N e a b hb)
  simpa only [homologyMap_comp] using h

end Typed

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev typed_chain :=
  Typed.chain p k n X (SheafProduct.OrderedComparison.target p k n X Y f I)
    (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
    (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I)
    (SheafProduct.OrderedComparison.map p k n X Y f hp I)
    (SheafGlobalData.Comparison.affineMap p k n X Y f hp I)
    (SheafProduct.OrderedComparison.affine_coordinate p k n X Y f hp I)

abbrev typed_homology_chain (q : ℕ) :=
  Typed.homology_chain p k n X (SheafProduct.OrderedComparison.target p k n X Y f I)
    (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
    (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I)
    (SheafProduct.OrderedComparison.map p k n X Y f hp I)
    (SheafGlobalData.Comparison.affineMap p k n X Y f hp I)
    (SheafProduct.OrderedComparison.affine_coordinate p k n X Y f hp I) q

end

/-! The ordinary homology comparison follows from the checked chain
square and the original bounded crystalline global comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem post_iso {C : Type*} [Category C] {A B D : C}
    (a : A ⟶ B) (e : B ≅ D) (b : A ⟶ D) (h : a ≫ e.hom = b) : a = b ≫ e.inv := by
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

private theorem paste_homology
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    {A B C D E F R : ModuleCat.{2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    (iso : C ≅ R) {native : A ⟶ D} {ordinary : D ⟶ E}
    {coordinates : A ⟶ B} {unit : B ⟶ F} {total : F ⟶ C}
    {product : C ⟶ E} {comparison : A ⟶ R}
    (hglobal : coordinates ≫ unit ≫ total ≫ iso.hom = comparison)
    (hchain : native ≫ ordinary = coordinates ≫ unit ≫ total ≫ product) :
    native ≫ ordinary = comparison ≫ iso.inv ≫ product := by
  have hc₀ : (coordinates ≫ unit ≫ total) ≫ iso.hom = comparison := by
    simpa only [Category.assoc] using hglobal
  have hc := post_iso _ iso comparison hc₀
  calc
    _ = (coordinates ≫ unit ≫ total) ≫ product := by
      simpa only [Category.assoc] using hchain
    _ = _ := by rw [hc, Category.assoc]

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev ordinary_homology (q : ℕ) :=
  paste_homology p k
    (product := homologyMap
      (ResolutionGlobal.smallProductIso p k n X Y f I).hom q)
    (ResolutionIntrinsicHomology.Intrinsic.iso p k n X Y f I q)
    (SheafGlobal.Comparison.homology_comparison p k n X Y f hp I q)
    (typed_homology_chain p k n X Y f hp I q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafHomologyData.OrderedComparison
