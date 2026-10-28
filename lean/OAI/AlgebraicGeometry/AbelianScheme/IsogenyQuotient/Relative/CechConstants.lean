import OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechTerms

/-! # Cech Constants -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechConstants.Construction

noncomputable section

/-! Literal base constants in the native relative structure-sheaf
Cech complex, with their affine-chart coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

open OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechTerms.Construction

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) {ι : Type u} [LinearOrder ι]
  (U : ι → X.Opens) (hU : iSup U = ⊤)

def relativeStructureConstants : R →ₗ[R] (FormalGeometry.Completion.RelativeStructureSections.Construction.relativeStructureSections f).obj (op ⊤) where
  toFun := FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤
  map_add' := map_add _
  map_smul' r s := by
    change FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤ (r * s) = FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤ r * FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤ s
    exact map_mul _ r s

def relativeCechConstants : R →ₗ[R] (FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X 0 :=
  ((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom.ker.subtype.comp
    ((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv f U hU).toLinearMap.comp (relativeStructureConstants f))

theorem relativeCechConstants_cycle (r : R) :
    (FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1 (relativeCechConstants f U hU r) = 0 :=
  (FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv f U hU (relativeStructureConstants f r)).property

set_option backward.isDefEq.respectTransparency false in
theorem relativeCechConstants_coordinate (r : R) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    Pi.π (FormalGeometry.Completion.RelativeCechTerms.Construction.relativeCechFactor f U 0) a
      ((FormalGeometry.Completion.RelativeCechTerms.Construction.relativeStructureCechTermIso f U 0).hom (relativeCechConstants f U hU r)) =
        FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f (∏ᶜ fun k : Fin 1 => U (a.val k)) r := by
  rw [FormalGeometry.Completion.RelativeCechTerms.Construction.relativeStructureCechTermIso_coordinate]
  change Pi.π (fun b : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 =>
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U 0 b.val) a
      (FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv f U hU (relativeStructureConstants f r)).val = _
  rw [FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv_coordinate]
  exact RingHom.congr_fun (FormalGeometry.Completion.Infinitesimal.ChartRestriction.Construction.baseOpenSectionsMap_restrict f le_top) r

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechConstants.Construction
