import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinarySectionMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ComplexBasisGluingLarge
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleOpenBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction

/-! # Model Sheaf Comparison -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelSheafComparison

noncomputable section

/-! The original affine native comparison glues to a map of the actual
Zariski sheaf complexes. Its restriction is the original frame map
conjugated by the canonical ordinary-form unit. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem conjugate_square {C : Type*} [Category C]
    {RA RB SA SB TA TB : C} (eA : RA ≅ SA) (eB : RB ≅ SB)
    (r : RB ⟶ RA) (s : SB ⟶ SA) (t : TB ⟶ TA)
    (a : RA ⟶ TA) (b : RB ⟶ TB)
    (hu : eB.hom ≫ s = r ≫ eA.hom) (hm : r ≫ a = b ≫ t) :
    (eB.inv ≫ b) ≫ t = s ≫ (eA.inv ≫ a) := by
  apply (cancel_epi eB.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc eB.hom s, hu]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hm.symm

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n

instance coefficients_sheafCompose :
    (Opens.grothendieckTopology X.left).HasSheafCompose
      (OrdinarySectionMap.Ordinary.coefficients p k n) := by
  let : PreservesLimitsOfSize.{0,0} (ModuleCat.uliftFunctor.{2,1} R) :=
    preservesLimitsOfSize_of_univLE.{1,1} _
  have : PreservesLimitsOfSize.{0,0}
      (OrdinarySectionMap.Ordinary.coefficients p k n) := by
    dsimp only [OrdinarySectionMap.Ordinary.coefficients,
      Principal.Comparison.coefficients,
      Crystalline.RelativeResolution.coefficientFunctor]
    infer_instance
  infer_instance

def sourceFunctor : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat S) ⥤
    Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{2} R) :=
  sheafCompose (Opens.grothendieckTopology X.left)
    (OrdinarySectionMap.Ordinary.coefficients p k n)

instance sourceFunctor_additive : (sourceFunctor p k n X).Additive where
  map_add := by intros; rfl

def source : CochainComplex (Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{2} R)) ℕ :=
  ((sourceFunctor p k n X).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex S X)

def targetFunctor : Sheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{2} R) ⥤
    Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{2} R) :=
  (TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous (ModuleCat.{2} R)
    (Opens.grothendieckTopology X.left) (Opens.grothendieckTopology Y.left)

instance targetFunctor_additive : (targetFunctor p k n X Y f).Additive where
  map_add := by intros; rfl

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def target : CochainComplex (Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{2} R)) ℕ :=
  ((targetFunctor p k n X Y f).mapHomologicalComplex (.up ℕ)).obj
    (BoundedOpen.FlasqueComplex.complex (Witt.Crystalline.wittStructureMap p k Y) n I)

def rawMap (U : X.left.affineOpens) :
    ((OrdinarySectionMap.Ordinary.coefficients p k n).mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex S (IntrinsicDeRham.SectionUnit.Intrinsic.ring S X U.val)) ⟶
      IntegralComparison.Sheaf.ComplexBasisGluingLarge.sections (ModuleCat.{2} R) X.left.carrier
        (target p k n X Y f I) U.val :=
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.evaluationIso (.up ℕ)
      (OrdinarySectionMap.Ordinary.rawDiagram p k n X) (op U)).inv ≫
    (((evaluation X.left.affineOpensᵒᵖ (ModuleCat.{2} R)).obj (op U)).mapHomologicalComplex
      (.up ℕ)).map (OrdinarySectionMap.Ordinary.map p k n X Y f hp I)

theorem raw_naturality {U V : X.left.affineOpens} (h : V ≤ U) :
    ((OrdinarySectionMap.Ordinary.coefficients p k n).mapHomologicalComplex (.up ℕ)).map
        (IntrinsicDeRham.SectionRestriction.IntrinsicUnit.nativeRestriction S X (homOfLE h)) ≫
      rawMap p k n X Y f hp I V =
    rawMap p k n X Y f hp I U ≫
      IntegralComparison.Sheaf.ComplexBasisGluingLarge.restriction (ModuleCat.{2} R) X.left.carrier
        (target p k n X Y f I) (homOfLE h) := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact ((OrdinarySectionMap.Ordinary.map p k n X Y f hp I).f q).naturality (homOfLE h).op

local instance coordinateOrder (a : Intrinsic.EtaleOpenBasis.Index (Truncated.Witt.Ring p k n) X) :
    LinearOrder (Intrinsic.EtaleOpenBasis.coordinateIndex S X a) :=
  Intrinsic.EtaleOpenBasis.coordinateOrder S X a

def basisUnit (a : Intrinsic.EtaleOpenBasis.Index (Truncated.Witt.Ring p k n) X) :
    ((OrdinarySectionMap.Ordinary.coefficients p k n).mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex S (IntrinsicDeRham.SectionUnit.Intrinsic.ring S X a.val)) ≅
      IntegralComparison.Sheaf.ComplexBasisGluingLarge.sections (ModuleCat.{2} R) X.left.carrier
        (source p k n X) a.val :=
  ((OrdinarySectionMap.Ordinary.coefficients p k n).mapHomologicalComplex (.up ℕ)).mapIso
    (IntrinsicDeRham.SectionUnit.Intrinsic.iso S X a.val a.property.1
      (Intrinsic.EtaleOpenBasis.coordinateIndex S X a))

def localMap (a : Intrinsic.EtaleOpenBasis.Index (Truncated.Witt.Ring p k n) X) :
    IntegralComparison.Sheaf.ComplexBasisGluingLarge.sections (ModuleCat.{2} R) X.left.carrier
        (source p k n X) a.val ⟶
      IntegralComparison.Sheaf.ComplexBasisGluingLarge.sections (ModuleCat.{2} R) X.left.carrier
        (target p k n X Y f I) a.val :=
  (basisUnit p k n X a).inv ≫ rawMap p k n X Y f hp I (Intrinsic.EtaleOpenBasis.affine S X a)

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] in
theorem basisUnit_naturality
    (a b : Intrinsic.EtaleOpenBasis.Index (Truncated.Witt.Ring p k n) X) (h : a.val ≤ b.val) :
    (basisUnit p k n X b).hom ≫
      IntegralComparison.Sheaf.ComplexBasisGluingLarge.restriction (ModuleCat.{2} R) X.left.carrier
        (source p k n X) (homOfLE h) =
    ((OrdinarySectionMap.Ordinary.coefficients p k n).mapHomologicalComplex (.up ℕ)).map
      (IntrinsicDeRham.SectionRestriction.IntrinsicUnit.nativeRestriction S X (homOfLE h)) ≫ (basisUnit p k n X a).hom := by
  let F := (OrdinarySectionMap.Ordinary.coefficients p k n).mapHomologicalComplex (.up ℕ)
  have hu := congrArg F.map (IntrinsicDeRham.SectionRestriction.IntrinsicUnit.unit_restriction S X
    (show a.val ⟶ b.val from homOfLE h))
  rw [Functor.map_comp, Functor.map_comp] at hu
  exact hu

theorem local_naturality (a b : Intrinsic.EtaleOpenBasis.Index (Truncated.Witt.Ring p k n) X) (h : a.val ≤ b.val) :
    localMap p k n X Y f hp I b ≫
        IntegralComparison.Sheaf.ComplexBasisGluingLarge.restriction (ModuleCat.{2} R) X.left.carrier
          (target p k n X Y f I) (homOfLE h) =
      IntegralComparison.Sheaf.ComplexBasisGluingLarge.restriction (ModuleCat.{2} R) X.left.carrier
          (source p k n X) (homOfLE h) ≫ localMap p k n X Y f hp I a := by

  exact conjugate_square (basisUnit p k n X a) (basisUnit p k n X b)
    (((OrdinarySectionMap.Ordinary.coefficients p k n).mapHomologicalComplex (.up ℕ)).map
      (IntrinsicDeRham.SectionRestriction.IntrinsicUnit.nativeRestriction S X (homOfLE h)))
    (IntegralComparison.Sheaf.ComplexBasisGluingLarge.restriction (ModuleCat.{2} R) X.left.carrier
      (source p k n X) (homOfLE h))
    (IntegralComparison.Sheaf.ComplexBasisGluingLarge.restriction (ModuleCat.{2} R) X.left.carrier
      (target p k n X Y f I) (homOfLE h))
    (rawMap p k n X Y f hp I (Intrinsic.EtaleOpenBasis.affine S X a))
    (rawMap p k n X Y f hp I (Intrinsic.EtaleOpenBasis.affine S X b))
    (basisUnit_naturality p k n X a b h)
    (raw_naturality p k n X Y f hp I
      (U := Intrinsic.EtaleOpenBasis.affine S X b)
      (V := Intrinsic.EtaleOpenBasis.affine S X a) h)

def basisMap : IntegralComparison.Sheaf.ComplexBasisGluingLarge.BasisMap
    (Intrinsic.EtaleOpenBasis.opens S X) (source p k n X) (target p k n X Y f I) where
  app := localMap p k n X Y f hp I
  naturality := local_naturality p k n X Y f hp I

def map : source p k n X ⟶ target p k n X Y f I :=
  (basisMap p k n X Y f hp I).glue (Intrinsic.EtaleOpenBasis.isBasis S X)

theorem map_app (a : Intrinsic.EtaleOpenBasis.Index (Truncated.Witt.Ring p k n) X) (q : ℕ) :
    ((ModelSheafComparison.map p k n X Y f hp I).f q).hom.app (op a.val) = (localMap p k n X Y f hp I a).f q :=
  (basisMap p k n X Y f hp I).glue_app (Intrinsic.EtaleOpenBasis.isBasis S X) q a

theorem unit_map (a : Intrinsic.EtaleOpenBasis.Index (Truncated.Witt.Ring p k n) X) (q : ℕ) :
    (OrdinarySectionMap.Ordinary.coefficients p k n).map
        ((IntrinsicDeRham.SectionUnit.Intrinsic.unit S X a.val).f q) ≫
      ((ModelSheafComparison.map p k n X Y f hp I).f q).hom.app (op a.val) =
    (rawMap p k n X Y f hp I (Intrinsic.EtaleOpenBasis.affine S X a)).f q := by
  rw [map_app]
  change ((basisUnit p k n X a).hom).f q ≫
    ((basisUnit p k n X a).inv ≫ rawMap p k n X Y f hp I
      (Intrinsic.EtaleOpenBasis.affine S X a)).f q = _
  simpa only [comp_f, Category.assoc] using congrArg (fun t => t.f q)
    (Iso.hom_inv_id_assoc (basisUnit p k n X a)
      (rawMap p k n X Y f hp I (Intrinsic.EtaleOpenBasis.affine S X a)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelSheafComparison
