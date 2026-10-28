import OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeStructureIntrinsic
import OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseCechGlobalSections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CochainScalarRestriction

/-! # Relative Cech Zero Cycles -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechZeroCycles.Construction

noncomputable section

/-! The native ordered structure-sheaf Cech complex and its global zero-cycles over the literal base ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The actual ordered Cech complex of the structure sheaf with scalars in R. -/
def relativeStructureCechComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainScalarRestriction.Construction.scalarRestrictedComplex (Scheme.ΓSpecIso (.of R)).inv.hom
    (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U)

/-- Literal global functions are exactly the zero-cycles of this actual R-linear complex. -/
def relativeStructureGlobalSectionsEquiv (hU : iSup U = ⊤) :
    (RelativeStructureSections.Construction.relativeStructureSections f).obj (op ⊤) ≃ₗ[R]
      ((relativeStructureCechComplex f U).d 0 1).hom.ker :=
  ((RelativeStructureIntrinsic.Construction.relativeStructureSectionsNativeIso f).app (op ⊤)).toLinearEquiv.trans
    ((((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).mapIso
      (BaseCechGlobalSections.Construction.orderedBaseGlobalSectionsLinearEquiv f
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U hU).toModuleIso).toLinearEquiv).trans
      (CochainScalarRestriction.Construction.scalarRestrictedZeroCyclesEquiv (Scheme.ΓSpecIso (.of R)).inv.hom
        (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U)))

theorem relativeStructureGlobalSectionsEquiv_coordinate (hU : iSup U = ⊤)
    (s : (RelativeStructureSections.Construction.relativeStructureSections f).obj (op ⊤)) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    (Pi.π (fun b : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 =>
      SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U 0 b.val) a)
        (relativeStructureGlobalSectionsEquiv f U hU s).val =
      X.presheaf.map (homOfLE (show (∏ᶜ fun k : Fin 1 => U (a.val k)) ≤ ⊤ from le_top)).op s :=
  BaseCechGlobalSections.Construction.orderedBaseGlobalSectionsLinearEquiv_coordinate f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U hU s a

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechZeroCycles.Construction
