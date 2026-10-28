import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionIntrinsicHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicConeCoordinates

/-! # Resolution Global -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionGlobal
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.HomologicalComplex
section

/-! The original bounded global complex and restriction cone, with
native source and target types fixed before the total comparison. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

def nativeGlobalIso : Presheaf.OrderedCechEdge.sections (CechIso.ResolutionGlobal.presheaf p k n X Y f I) ≅
    CechIso.ResolutionGlobal.nativeGlobalComplex p k n Y I :=
  CechIso.ResolutionGlobal.globalIso p k n X Y f I

def nativeCone :
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X.left.affineOpens)).obj
      (CechIso.ResolutionGlobal.nativeGlobalComplex p k n Y I) ⟶ CechIso.ResolutionGlobal.nativeSections p k n X Y f I :=
  GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.cone (Witt.Crystalline.wittStructureMap p k Y) n I
    (SectionBifunctor.specialOpens p k n X Y f)

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem native_cone :
    nativeCone p k n X Y f I ≫ (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I).hom =
    GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant.map (nativeGlobalIso p k n X Y f I).inv ≫
      Small.PresheafConeCoordinates.cone (Truncated.Witt.Ring p k n) X
        (CechIso.ResolutionGlobal.presheaf p k n X Y f I) :=
  CechIso.ResolutionGlobal.affine_cone p k n X Y f I

end

section

/-! The original native edge and its global homology square, with the
bounded global complex and cone expressed in their native coordinates. -/
open Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

attribute [local instance] CechIso.ResolutionGlobal.tuple_preserves CechIso.ResolutionGlobal.special_tuple_preserves

def affineTotalIso :
    (Small.OrdinaryCechCoefficientUnit.Ordinary.affineTotal
      (D := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
      (Truncated.Witt.Ring p k n) X).obj (CechIso.ResolutionGlobal.nativeSections p k n X Y f I) ≅
    (Small.OrdinaryCechCoefficientUnit.Ordinary.affineTotal
      (D := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
      (Truncated.Witt.Ring p k n) X).obj (CechIso.ResolutionGlobal.pulledSections p k n X Y f I) :=
  CechIso.Map.mapIso p k n X
    (CechIso.ResolutionGlobal.nativeSections p k n X Y f I) (CechIso.ResolutionGlobal.pulledSections p k n X Y f I)
    (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I)

def smallProductIso :
    FrameCech.Complexes.target p k n X Y f I ≅
    IntrinsicConeCoordinates.Intrinsic.ordinaryTotal p k n X (CechIso.ResolutionGlobal.presheaf p k n X Y f I) :=
  IntrinsicConeCoordinates.Intrinsic.productIso p k n X
    (CechIso.ResolutionGlobal.presheaf p k n X Y f I) (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
    (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I)

def nativeEdge :
    CechIso.ResolutionGlobal.nativeGlobalComplex p k n Y I ⟶
    FrameCech.Complexes.target p k n X Y f I :=
  GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.map (Witt.Crystalline.wittStructureMap p k Y) n I
    (SectionBifunctor.specialOpens p k n X Y f)
    (CechSliceResolution.opens p k n X)

omit [Fintype k] [IsSeparated Y.hom] in
theorem nativeEdge_eq : nativeEdge p k n X Y f I =
    IntrinsicConeCoordinates.Intrinsic.edge p k n X
      (CechIso.ResolutionGlobal.nativeSections p k n X Y f I) (CechIso.ResolutionGlobal.nativeGlobalComplex p k n Y I)
      (nativeCone p k n X Y f I) := rfl

attribute [local irreducible] HomologicalComplex.homology

omit [Fintype k] [IsSeparated Y.hom] in
theorem small_global_homology (q : ℕ) :
    (homologyMap (CechIso.ResolutionGlobal.globalIso p k n X Y f I).hom q ≫ homologyMap (nativeEdge p k n X Y f I) q) ≫
      (ResolutionIntrinsicHomology.Intrinsic.iso p k n X Y f I q).hom =
    (CechIso.ResolutionGlobal.globalHomologyIso p k n X Y f I q).hom := by
  have h := GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.homology
    (Witt.Crystalline.wittStructureMap p k Y) n I
    (SectionBifunctor.specialOpens p k n X Y f)
    (CechSliceResolution.opens p k n X)
    (GlobalEdge.InjectiveCech.cover p k n X Y f) q
  exact (Category.assoc _ _ _).trans
    (congrArg (fun a => homologyMap (CechIso.ResolutionGlobal.globalIso p k n X Y f I).hom q ≫ a) h)

end

section

/-! The original cochain maps and direct native homology square,
before replacing any map under the homology functor. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem global_coordinate : (CechIso.ResolutionGlobal.globalIso p k n X Y f I).hom =
    (nativeGlobalIso p k n X Y f I).hom := rfl

omit [Fintype k] [IsSeparated Y.hom] in
theorem product_coordinate : (smallProductIso p k n X Y f I).hom =
    (IntrinsicConeCoordinates.Intrinsic.productIso p k n X
      (CechIso.ResolutionGlobal.presheaf p k n X Y f I) (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
      (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I)).hom := rfl

attribute [local irreducible] HomologicalComplex.homology

omit [Fintype k] [IsSeparated Y.hom] in
theorem cone_homology (q : ℕ) :
    (homologyMap (nativeGlobalIso p k n X Y f I).hom q ≫
      homologyMap (IntrinsicConeCoordinates.Intrinsic.edge p k n X
        (CechIso.ResolutionGlobal.nativeSections p k n X Y f I) (CechIso.ResolutionGlobal.nativeGlobalComplex p k n Y I)
        (nativeCone p k n X Y f I)) q) ≫
      homologyMap (IntrinsicConeCoordinates.Intrinsic.productIso p k n X
        (CechIso.ResolutionGlobal.presheaf p k n X Y f I) (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
        (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I)).hom q =
    homologyMap (Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) (CechIso.ResolutionGlobal.presheaf p k n X Y f I)) q :=
  IntrinsicConeCoordinates.Intrinsic.homology p k n X
    (CechIso.ResolutionGlobal.presheaf p k n X Y f I) (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
    (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I) (CechIso.ResolutionGlobal.nativeGlobalComplex p k n Y I)
    (nativeGlobalIso p k n X Y f I).symm (nativeCone p k n X Y f I)
    (native_cone p k n X Y f I) q

end

section

/-! Explicit transport between the original native total and the
cone total, before applying homology. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

def nativeTotalIso :
    FrameCech.Complexes.target p k n X Y f I ≅
      IntrinsicConeCoordinates.Intrinsic.total p k n X
        (CechIso.ResolutionGlobal.nativeSections p k n X Y f I) := Iso.refl _

omit [Fintype k] [IsSeparated Y.hom] in
theorem native_edge_square :
    nativeEdge p k n X Y f I ≫ (nativeTotalIso p k n X Y f I).hom =
      IntrinsicConeCoordinates.Intrinsic.edge p k n X
        (CechIso.ResolutionGlobal.nativeSections p k n X Y f I) (CechIso.ResolutionGlobal.nativeGlobalComplex p k n Y I)
        (nativeCone p k n X Y f I) := by
  change nativeEdge p k n X Y f I ≫ 𝟙 _ = _
  exact (Category.comp_id _).trans (nativeEdge_eq p k n X Y f I)

omit [Fintype k] [IsSeparated Y.hom] in
theorem native_product_square :
    (smallProductIso p k n X Y f I).hom =
      (nativeTotalIso p k n X Y f I).hom ≫
        (IntrinsicConeCoordinates.Intrinsic.productIso p k n X
          (CechIso.ResolutionGlobal.presheaf p k n X Y f I) (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
          (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I)).hom := by
  change (smallProductIso p k n X Y f I).hom = 𝟙 _ ≫ _
  exact (product_coordinate p k n X Y f I).trans (Category.id_comp _).symm

end

/-! The actual native cone comparison before composing global coordinates. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

omit [Fintype k] [IsSeparated Y.hom] in
theorem cone_comparison :
    IntrinsicConeCoordinates.Intrinsic.edge p k n X
      (CechIso.ResolutionGlobal.nativeSections p k n X Y f I) (CechIso.ResolutionGlobal.nativeGlobalComplex p k n Y I)
      (nativeCone p k n X Y f I) ≫
      (IntrinsicConeCoordinates.Intrinsic.productIso p k n X
        (CechIso.ResolutionGlobal.presheaf p k n X Y f I) (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
        (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I)).hom =
    (nativeGlobalIso p k n X Y f I).inv ≫
      Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) (CechIso.ResolutionGlobal.presheaf p k n X Y f I) :=
  IntrinsicConeCoordinates.Intrinsic.comparison p k n X
    (CechIso.ResolutionGlobal.presheaf p k n X Y f I) (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
    (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I) (CechIso.ResolutionGlobal.nativeGlobalComplex p k n Y I)
    (nativeGlobalIso p k n X Y f I).symm (nativeCone p k n X Y f I)
    (native_cone p k n X Y f I)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionGlobal

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionGlobal.CochainSquare

/-! Paste the checked native cone square through the actual total
coordinates before applying any homology functor. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionGlobal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem paste {C : Type*} [Category C] {R A B B' T : C}
    (e : R ≅ A) {a : A ⟶ B} {a' : A ⟶ B'} {t : B ⟶ B'}
    {b : B ⟶ T} {b' : B' ⟶ T} {o : R ⟶ T}
    (ha : a ≫ t = a') (hb : b = t ≫ b') (h : a' ≫ b' = e.inv ≫ o) :
    (e.hom ≫ a) ≫ b = o := by
  calc
    (e.hom ≫ a) ≫ b = e.hom ≫ ((a ≫ t) ≫ b') := by
      rw [hb]
      simp only [Category.assoc]
    _ = e.hom ≫ (a' ≫ b') := by rw [ha]
    _ = o := by rw [h]; simp only [Iso.hom_inv_id_assoc]

namespace Typed

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (K : CochainComplex (X.left.Opensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)

/-- The original ordinary edge with its native module category fixed
before substituting the crystalline resolution. -/
def ordinary : Presheaf.OrderedCechEdge.sections K ⟶
    IntrinsicConeCoordinates.Intrinsic.ordinaryTotal p k n X K :=
  Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K

omit [Fintype k] [CharP k p] [X.left.IsSeparated] in
theorem homology (q : ℕ) :
    homologyMap (ordinary p k n X K) q =
      homologyMap (Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K) q := rfl

variable (N : CochainComplex (X.left.affineOpensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
  (eN : N ≅ ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
    (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).obj K)
  (M : CochainComplex (ModuleCat.{2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
  (eM : M ≅ Presheaf.OrderedCechEdge.sections K)
  (η : GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant.obj M ⟶ N)
  (hη : η ≫ eN.hom = GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant.map eM.hom ≫
    Small.PresheafConeCoordinates.cone (Truncated.Witt.Ring p k n) X K)

include hη in
omit [Fintype k] [CharP k p] in
theorem comparison :
    IntrinsicConeCoordinates.Intrinsic.edge p k n X N M η ≫
      (IntrinsicConeCoordinates.Intrinsic.productIso p k n X K N eN).hom =
    eM.hom ≫ ordinary p k n X K :=
  IntrinsicConeCoordinates.Intrinsic.comparison p k n X K N eN M eM η hη

end Typed

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

attribute [local irreducible] nativeGlobalIso nativeEdge smallProductIso nativeTotalIso
  IntrinsicConeCoordinates.Intrinsic.edge IntrinsicConeCoordinates.Intrinsic.productIso
  Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary

omit [IsSeparated Y.hom] in
omit [Fintype k] in
theorem typed_cone_comparison :
    IntrinsicConeCoordinates.Intrinsic.edge p k n X
      (CechIso.ResolutionGlobal.nativeSections p k n X Y f I) (CechIso.ResolutionGlobal.nativeGlobalComplex p k n Y I)
      (nativeCone p k n X Y f I) ≫
      (IntrinsicConeCoordinates.Intrinsic.productIso p k n X
        (CechIso.ResolutionGlobal.presheaf p k n X Y f I) (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
        (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I)).hom =
    (nativeGlobalIso p k n X Y f I).inv ≫
      Typed.ordinary p k n X (CechIso.ResolutionGlobal.presheaf p k n X Y f I) :=
  Typed.comparison p k n X
    (CechIso.ResolutionGlobal.presheaf p k n X Y f I) (CechIso.ResolutionGlobal.nativeSections p k n X Y f I)
    (CechIso.ResolutionGlobal.affineSectionsIso p k n X Y f I) (CechIso.ResolutionGlobal.nativeGlobalComplex p k n Y I)
    (nativeGlobalIso p k n X Y f I).symm (nativeCone p k n X Y f I)
    (native_cone p k n X Y f I)

abbrev comparison :=
  paste (nativeGlobalIso p k n X Y f I)
    (native_edge_square p k n X Y f I)
    (native_product_square p k n X Y f I)
    (typed_cone_comparison p k n X Y f I)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionGlobal.CochainSquare

end

end OAI
