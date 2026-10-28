import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelSheafComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrdinaryOrderedEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechCoefficientUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeNaturality

/-! # Cech Iso -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechIso.ResolutionGlobal

/-! The global sections and ordered Čech edge of the actual pushed
native resolution, with their original bounded crystalline target. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev presheaf := ((sheafToPresheaf (Opens.grothendieckTopology X.left)
    (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))).mapHomologicalComplex
      (.up ℕ)).obj (ModelSheafComparison.target p k n X Y f I)

def nativeGlobalComplex : CochainComplex
    (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) (⊤ : Y.left.Opens)).mapHomologicalComplex
    (.up ℕ)).obj (BoundedOpen.SectionComplex.complex (Witt.Crystalline.wittStructureMap p k Y) n I)

def globalIso : Presheaf.OrderedCechEdge.sections (presheaf p k n X Y f I) ≅
    nativeGlobalComplex p k n Y I :=
  Iso.refl _

def globalHomologyIso (q : ℕ) :=
  (HomologicalComplex.homologyFunctor _ _ q).mapIso (globalIso p k n X Y f I) ≪≫
    BoundedOpen.SectionGlobal.homologyIso (Witt.Crystalline.wittStructureMap p k Y) n I q

variable {ι : Type} [LinearOrder ι] (V : ι → X.left.Opens)

def toOrdered (q : ℕ) := (globalHomologyIso p k n X Y f I q).inv ≫
  homologyMap (Presheaf.OrderedCechEdge.edge V (presheaf p k n X Y f I)) q

local instance tuple_preserves (m : ℕ)
    (t : Fin (m+1) → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X) :
    PreservesLimit (Discrete.functor (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X ∘ t))
      (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.inclusion_preserves X.left _
local instance special_tuple_preserves (m : ℕ)
    (t : Fin (m+1) → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X) :
    PreservesLimit (Discrete.functor (CechSliceResolution.opens p k n X ∘ t))
      (SectionBifunctor.specialOpens p k n X Y f) :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.composite_preserves X.left Y.left f _

abbrev nativeSections := ((SectionBifunctor.sections p k n X Y f).mapHomologicalComplex
  (.up ℕ)).obj I.cocomplex
abbrev pulledSections := ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
  (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).obj (presheaf p k n X Y f I)

def affineSectionsIso : nativeSections p k n X Y f I ≅ pulledSections p k n X Y f I := Iso.refl _

def affineCone := GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)
  (presheaf p k n X Y f I) (Presheaf.OrderedCechEdge.sections (presheaf p k n X Y f I))
  (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone X.left.Opens (presheaf p k n X Y f I))

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem affine_cone :
    GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.cone (Witt.Crystalline.wittStructureMap p k Y) n I
      (SectionBifunctor.specialOpens p k n X Y f) ≫
        (affineSectionsIso p k n X Y f I).hom =
    GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant.map (globalIso p k n X Y f I).inv ≫
      affineCone p k n X Y f I := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechIso.ResolutionGlobal

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechIso.Map

/-! Mapping an affine-complex isomorphism to the native small Cech total,
with the actual coefficient category fixed before the resolution input. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (K L : CochainComplex (X.left.affineOpensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
  (e : K ≅ L)

def mapIso :
    (Small.OrdinaryCechCoefficientUnit.Ordinary.affineTotal (Truncated.Witt.Ring p k n) X).obj K ≅
    (Small.OrdinaryCechCoefficientUnit.Ordinary.affineTotal (Truncated.Witt.Ring p k n) X).obj L :=
  (Small.OrdinaryCechCoefficientUnit.Ordinary.affineTotal (Truncated.Witt.Ring p k n) X).mapIso e

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechIso.Map

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechIso.Product

/-! The small-cover product isomorphism, with the native coefficient
category fixed before choosing the actual crystalline resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (K : CochainComplex (X.left.Opensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
  (N : CochainComplex (X.left.affineOpensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
  (e : N ≅ ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
    (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).obj K)

def iso :
    (Small.OrdinaryCechCoefficientUnit.Ordinary.affineTotal (Truncated.Witt.Ring p k n) X).obj N ≅
    (OrderedCech.TotalProjection.ordinary
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)).obj K :=
  Map.mapIso p k n X N _ e ≪≫
    Small.OrdinaryCechCoefficientUnit.Ordinary.productIso (Truncated.Witt.Ring p k n) X K

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechIso.Product

end

end OAI
