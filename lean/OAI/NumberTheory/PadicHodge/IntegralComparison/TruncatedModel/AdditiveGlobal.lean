import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueOrderedGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.EdgeCoefficientHomology

/-! # Additive Global -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveGlobal.ResolutionFlasque

/-! Every genuine open cover gives an invertible global edge for the
actual pushed bounded crystalline resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev linear := CechIso.ResolutionGlobal.presheaf p k n X Y f I
abbrev target := AdditiveTop.Comparison.target p k n X Y f I

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem term_flasque (q : ℕ) : TopCat.Presheaf.IsFlasque (X := X.left.toTopCat)
    ((ModelSheafComparison.target p k n X Y f I).X q).obj := by
  let := BoundedOpen.FlasqueComplex.term_flasque
    (Witt.Crystalline.wittStructureMap p k Y) n I q
  constructor
  intro U V a
  change Epi (((BoundedOpen.FlasqueComplex.complex
    (Witt.Crystalline.wittStructureMap p k Y) n I).X q).obj.map
      ((TopologicalSpace.Opens.map f.base).op.map a))
  infer_instance

variable {ι : Type} [LinearOrder ι] (V : ι → X.left.Opens) (hV : iSup V = ⊤)

include hV in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem linear_edge_isIso (q : ℕ) :
    IsIso (homologyMap (IntegralComparison.Presheaf.OrderedCechEdge.edge V (linear p k n X Y f I)) q) :=
  FlasqueOrderedGlobal.homology_isIso.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) X.left.toTopCat V
    (ModelSheafComparison.target p k n X Y f I) hV
    (term_flasque p k n X Y f I) q

include hV in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem additive_edge_isIso (q : ℕ) :
    IsIso (homologyMap (IntegralComparison.Presheaf.OrderedCechEdge.edge V (target p k n X Y f I)) q) := by
  let := linear_edge_isIso p k n X Y f I V hV q
  exact FlasqueOrderedGlobal.EdgeCoefficient.homology_isIso V
    (AdditiveTop.Comparison.forget p k) (linear p k n X Y f I) q

include hV in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem toOrdered_isIso (q : ℕ) :
    IsIso (CechIso.ResolutionGlobal.toOrdered p k n X Y f I V q) := by
  let := linear_edge_isIso p k n X Y f I V hV q
  change IsIso ((CechIso.ResolutionGlobal.globalHomologyIso p k n X Y f I q).inv ≫
    homologyMap (IntegralComparison.Presheaf.OrderedCechEdge.edge V (linear p k n X Y f I)) q)
  infer_instance

include hV in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem toOrdered_injective (q : ℕ) :
    Function.Injective (CechIso.ResolutionGlobal.toOrdered p k n X Y f I V q) := by
  let := toOrdered_isIso p k n X Y f I V hV q
  exact (ConcreteCategory.bijective_of_isIso
    (CechIso.ResolutionGlobal.toOrdered p k n X Y f I V q)).injective

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveGlobal.ResolutionFlasque

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveGlobal

/-! The original bounded crystalline global edge after forgetting
scalars, identified with the literal additive resolution edge. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev forget := AdditiveTop.Comparison.forget p k
abbrev linear := CechIso.ResolutionGlobal.presheaf p k n X Y f I
abbrev target := AdditiveTop.Comparison.target p k n X Y f I

def globalHomologyIso (q : ℕ) :=
  ((IntegralComparison.Presheaf.OrderedCechEdge.sections (linear p k n X Y f I)).sc q).mapHomologyIso (forget p k) ≪≫
    (forget p k).mapIso (CechIso.ResolutionGlobal.globalHomologyIso p k n X Y f I q)

variable {ι : Type} [LinearOrder ι] (V : ι → X.left.Opens)

def orderedIso (q : ℕ) := OrderedCech.CoefficientTotal.homologyIso V (forget p k)
  (linear p k n X Y f I) q

def toOrdered (q : ℕ) :=
  (forget p k).map (CechIso.ResolutionGlobal.toOrdered p k n X Y f I V q) ≫
    (orderedIso p k n X Y f I V q).hom

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem literal (q : ℕ) : toOrdered p k n X Y f I V q =
    (globalHomologyIso p k n X Y f I q).inv ≫
      homologyMap (IntegralComparison.Presheaf.OrderedCechEdge.edge V (target p k n X Y f I)) q := by
  unfold toOrdered CechIso.ResolutionGlobal.toOrdered globalHomologyIso
  simp only [Functor.map_comp, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  exact congrArg (fun a =>
    (forget p k).map (CechIso.ResolutionGlobal.globalHomologyIso p k n X Y f I q).inv ≫ a)
    (Ordered.EdgeCoefficientHomology.homology V (forget p k) (linear p k n X Y f I) q)

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem toOrdered_isIso (hV : iSup V = ⊤) (q : ℕ) :
    IsIso (toOrdered p k n X Y f I V q) := by
  let := ResolutionFlasque.toOrdered_isIso p k n X Y f I V hV q
  dsimp only [toOrdered]
  infer_instance

def coverIso (hV : iSup V = ⊤) (q : ℕ) := by
  let := toOrdered_isIso p k n X Y f I V hV q
  exact asIso (toOrdered p k n X Y f I V q)

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem cover_injective (hV : iSup V = ⊤) (q : ℕ) :
    Function.Injective (toOrdered p k n X Y f I V q) := by
  let := toOrdered_isIso p k n X Y f I V hV q
  exact (ConcreteCategory.bijective_of_isIso (toOrdered p k n X Y f I V q)).injective

def smallIso (q : ℕ) := coverIso p k n X Y f I
  (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)
  (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (Truncated.Witt.Ring p k n) X) q

omit [Fintype k] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem smallIso_hom (q : ℕ) : (smallIso p k n X Y f I q).hom =
    toOrdered p k n X Y f I (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) q := rfl

omit [Fintype k] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem injective (q : ℕ) : Function.Injective
    (toOrdered p k n X Y f I (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) q) :=
  cover_injective p k n X Y f I (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (Truncated.Witt.Ring p k n) X) q

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveGlobal

end

end OAI
