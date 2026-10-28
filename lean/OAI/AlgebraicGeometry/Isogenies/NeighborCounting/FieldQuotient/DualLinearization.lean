import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualCover
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActionLaws
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.GlobalLineDescent

/-! # Dual Linearization -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualLinearization

noncomputable section

/-! The proved normalized family transports supply the unit and cocycle
of an actual kernel-action linearization for the Poincare cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ActionMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

theorem kernelAction_sameImage {S : Scheme.{u}} {V W : Over S}
    [GrpObj V] [GrpObj W] (p : V ⟶ W) [IsMonHom p] :
    Picard.PoincareBundle.Kernel.ActionMaps.source p ≫ p = Picard.PoincareBundle.Kernel.ActionMaps.action p ≫ p := by
  rw [Picard.PoincareBundle.Kernel.ActionMaps.action, MonObj.mul_comp, Category.assoc, Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.comp_one, mul_one]

theorem sameImage_precomp {C : Type*} [Category* C] {V W T U : C}
    (p : V ⟶ W) (x y : T ⟶ V) (h : x ≫ p = y ≫ p)
    (t : U ⟶ T) (x' y' : U ⟶ V) (hx : t ≫ x = x') (hy : t ≫ y = y') :
    x' ≫ p = y' ≫ p := by
  rw [← hx, ← hy, Category.assoc, Category.assoc, h]

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActionLaws.Construction (KernelActionUnit kernelActionCocycle_of_pullIso kernelActionLinearization)

variable {k : Type} [Field k] {d : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

local instance compactOfProper (T : Over (Spec (.of k))) [IsProper T.hom] : CompactSpace T.left :=
  QuasiCompact.compactSpace_of_compactSpace T.hom

local instance quasiSeparatedOfProper (T : Over (Spec (.of k))) [IsProper T.hom] : QuasiSeparatedSpace T.left :=
  quasiSeparatedSpace_of_quasiSeparated T.hom

def quotientDualPoincareActionIso :
    Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (DualSheaf.quotientDualSourcePoincare D f))
        (Picard.PoincareBundle.Kernel.ActionMaps.source (DualCover.quotientDualPoincareCover D f)) ≅
      Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (DualSheaf.quotientDualSourcePoincare D f))
        (Picard.PoincareBundle.Kernel.ActionMaps.action (DualCover.quotientDualPoincareCover D f)) :=
  DualPointTransport.quotientDualPointIso D f r _ (Picard.PoincareBundle.Kernel.ActionMaps.source (DualCover.quotientDualPoincareCover D f))
    (Picard.PoincareBundle.Kernel.ActionMaps.action (DualCover.quotientDualPoincareCover D f)) (kernelAction_sameImage (DualCover.quotientDualPoincareCover D f))

theorem quotientDualPoincareAction_unit :
    AbelianScheme.FrobeniusKernel.ActionLaws.Construction.KernelActionUnit (DualCover.quotientDualPoincareCover D f) (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of k)))
      (DualSheaf.quotientDualSourcePoincare D f).sheaf (quotientDualPoincareActionIso D f r) := by
  let p := DualCover.quotientDualPoincareCover D f
  have hn := congrArg Iso.hom (DualPointNaturality.quotientDualPointIso_pullback D f r
    (Picard.PoincareBundle.Kernel.ActionMaps.source p) (Picard.PoincareBundle.Kernel.ActionMaps.action p) (kernelAction_sameImage p) (Picard.PoincareBundle.Kernel.ActionMaps.unitSection p)
    (𝟙 _) (𝟙 _) (Picard.PoincareBundle.Kernel.ActionMaps.unitSection_source p) (Picard.PoincareBundle.Kernel.ActionMaps.unitSection_action p) rfl)
  exact hn.trans (congrArg Iso.hom (DualPointTransport.quotientDualPointIso_self D f r _ (𝟙 _)))

abbrev quotientDualTripleSourceMiddle :=
  sameImage_precomp (DualCover.quotientDualPoincareCover D f)
    (Picard.PoincareBundle.Kernel.ActionMaps.source (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.action (DualCover.quotientDualPoincareCover D f))
    (kernelAction_sameImage (DualCover.quotientDualPoincareCover D f))
    (Picard.PoincareBundle.Kernel.ActionMaps.firstStep (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.tripleSource (DualCover.quotientDualPoincareCover D f))
    (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle (DualCover.quotientDualPoincareCover D f)) rfl rfl

abbrev quotientDualTripleMiddleTarget :=
  sameImage_precomp (DualCover.quotientDualPoincareCover D f)
    (Picard.PoincareBundle.Kernel.ActionMaps.source (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.action (DualCover.quotientDualPoincareCover D f))
    (kernelAction_sameImage (DualCover.quotientDualPoincareCover D f))
    (Picard.PoincareBundle.Kernel.ActionMaps.secondStep (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle (DualCover.quotientDualPoincareCover D f))
    (Picard.PoincareBundle.Kernel.ActionMaps.tripleTarget (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.secondStep_source (DualCover.quotientDualPoincareCover D f)) rfl

abbrev quotientDualTripleFirstIso := DualPointTransport.quotientDualPointIso D f r _
  (Picard.PoincareBundle.Kernel.ActionMaps.tripleSource (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle (DualCover.quotientDualPoincareCover D f))
  (quotientDualTripleSourceMiddle D f)

abbrev quotientDualTripleSecondIso := DualPointTransport.quotientDualPointIso D f r _
  (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.tripleTarget (DualCover.quotientDualPoincareCover D f))
  (quotientDualTripleMiddleTarget D f)

abbrev quotientDualTripleCompositeIso := DualPointTransport.quotientDualPointIso D f r _
  (Picard.PoincareBundle.Kernel.ActionMaps.tripleSource (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.tripleTarget (DualCover.quotientDualPoincareCover D f))
  ((quotientDualTripleSourceMiddle D f).trans (quotientDualTripleMiddleTarget D f))

abbrev quotientDualPoincareAction_cocycle :=
  AbelianScheme.FrobeniusKernel.ActionLaws.Construction.kernelActionCocycle_of_pullIso (DualCover.quotientDualPoincareCover D f) (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of k)))
    (DualSheaf.quotientDualSourcePoincare D f).sheaf (quotientDualPoincareActionIso D f r)
    (quotientDualTripleFirstIso D f r) (quotientDualTripleSecondIso D f r) (quotientDualTripleCompositeIso D f r)
    (DualPointNaturality.quotientDualPointIso_pullback D f r
      (Picard.PoincareBundle.Kernel.ActionMaps.source (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.action (DualCover.quotientDualPoincareCover D f))
      (kernelAction_sameImage (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.firstStep (DualCover.quotientDualPoincareCover D f))
      (Picard.PoincareBundle.Kernel.ActionMaps.tripleSource (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle (DualCover.quotientDualPoincareCover D f))
      rfl rfl (quotientDualTripleSourceMiddle D f))
    (DualPointNaturality.quotientDualPointIso_pullback D f r
      (Picard.PoincareBundle.Kernel.ActionMaps.source (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.action (DualCover.quotientDualPoincareCover D f))
      (kernelAction_sameImage (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.secondStep (DualCover.quotientDualPoincareCover D f))
      (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.tripleTarget (DualCover.quotientDualPoincareCover D f))
      (Picard.PoincareBundle.Kernel.ActionMaps.secondStep_source (DualCover.quotientDualPoincareCover D f)) rfl (quotientDualTripleMiddleTarget D f))
    (DualPointNaturality.quotientDualPointIso_pullback D f r
      (Picard.PoincareBundle.Kernel.ActionMaps.source (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.action (DualCover.quotientDualPoincareCover D f))
      (kernelAction_sameImage (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.productStep (DualCover.quotientDualPoincareCover D f))
      (Picard.PoincareBundle.Kernel.ActionMaps.tripleSource (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.tripleTarget (DualCover.quotientDualPoincareCover D f))
      (Picard.PoincareBundle.Kernel.ActionMaps.productStep_source (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.productStep_action (DualCover.quotientDualPoincareCover D f))
      ((quotientDualTripleSourceMiddle D f).trans (quotientDualTripleMiddleTarget D f)))
    (DualCover.quotientDualPointIso_comp D f r _ (Picard.PoincareBundle.Kernel.ActionMaps.tripleSource (DualCover.quotientDualPoincareCover D f))
      (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle (DualCover.quotientDualPoincareCover D f)) (Picard.PoincareBundle.Kernel.ActionMaps.tripleTarget (DualCover.quotientDualPoincareCover D f))
      (quotientDualTripleSourceMiddle D f) (quotientDualTripleMiddleTarget D f))

def quotientDualPoincareLinearization :
    Picard.PoincareBundle.Geometric.KernelLinearization.LineLinearization (DualCover.quotientDualPoincareCover D f)
      (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (DualSheaf.quotientDualSourcePoincare D f)) :=
  AbelianScheme.FrobeniusKernel.ActionLaws.Construction.kernelActionLinearization (DualCover.quotientDualPoincareCover D f) (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of k)))
    (DualSheaf.quotientDualSourcePoincare D f).sheaf (quotientDualPoincareActionIso D f r)
    (quotientDualPoincareAction_unit D f r) (quotientDualPoincareAction_cocycle D f r)

def quotientDualDescendedPoincare :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme ⊗ B.scheme).left :=
  Picard.PoincareBundle.Line.Comparison.Bundle.toShared (Picard.PoincareBundle.Kernel.GlobalLineDescent.descendedLine
    (DualCover.quotientDualPoincareCover D f) (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (DualSheaf.quotientDualSourcePoincare D f))
    (quotientDualPoincareLinearization D f r))

def quotientDualDescendedPoincare_pullbackIso :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DualCover.quotientDualPoincareCover D f).left (quotientDualDescendedPoincare D f r)).sheaf ≅
      (DualSheaf.quotientDualSourcePoincare D f).sheaf :=
  Picard.PoincareBundle.Kernel.GlobalLineDescent.pullbackIso
    (DualCover.quotientDualPoincareCover D f) (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (DualSheaf.quotientDualSourcePoincare D f))
    (quotientDualPoincareLinearization D f r)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualLinearization
