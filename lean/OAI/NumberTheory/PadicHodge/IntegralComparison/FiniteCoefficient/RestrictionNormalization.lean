import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.CoefficientMaps

/-! # Restriction Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.RestrictionNormalization

noncomputable section

/-! The coefficient restriction maps used in local duality are the
literal restriction of functions. Their quotient-module multiplication
compatibility is the original scheme morphism's naturality square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections

variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
  (i : X ⟶ Z) [IsClosedImmersion i]

abbrev scalarSheaf := Global.StructureUnit.directImage i
abbrev coefficientSheaf := Cech.StructurePullbackUnit.coefficients f i

local instance : (scalarSheaf i).IsQuasicoherent := by
  let : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i
local instance : (coefficientSheaf f i).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f i

attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra

variable (U : Z.Opens) (hU : IsAffineOpen U)

def scalarLiteralIso :
    (Affine.ModuleExactSections.sections U).obj (scalarSheaf i) ≅
      ModuleCat.of Γ(Z, U) (Finite.FlatCoefficientSections.quotientRing i U) :=
  (show Γ(scalarSheaf i, U) ≃ₗ[Γ(Z, U)] Finite.FlatCoefficientSections.quotientRing i U from
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toModuleIso

def scalarChartIso :
    (AffineOpen.InternalHom.sections U hU).obj (scalarSheaf i) ≅
      ModuleCat.of Γ(Z, U) (Finite.FlatCoefficientSections.quotientRing i U) :=
  (Affine.ChartSections.iso U hU (scalarSheaf i)).symm ≪≫ scalarLiteralIso i U

variable (r : Γ(Z, U))

abbrev scalarRestriction := AffinePrincipal.CoefficientMaps.restriction U hU r (scalarSheaf i)
  (ModuleCat.of Γ(Z, U) (Finite.FlatCoefficientSections.quotientRing i U))
  (ModuleCat.of Γ(Z, AffinePrincipal.Sections.openSubset U r) (Finite.FlatCoefficientSections.quotientRing i (AffinePrincipal.Sections.openSubset U r)))
  (scalarChartIso i U hU) (scalarChartIso i (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))

abbrev coefficientRestriction := AffinePrincipal.CoefficientMaps.restriction U hU r (coefficientSheaf f i)
  (ModuleCat.of Γ(Z, U) (Finite.FlatCoefficientSections.coefficientRing f i U))
  (ModuleCat.of Γ(Z, AffinePrincipal.Sections.openSubset U r) (Finite.FlatCoefficientSections.coefficientRing f i (AffinePrincipal.Sections.openSubset U r)))
  (Finite.FlatCoefficientSections.chartIso f i U hU) (Finite.FlatCoefficientSections.chartIso f i (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r))

omit [IsClosedImmersion i] in
theorem scalar_restriction (q : Finite.FlatCoefficientSections.quotientRing i U) :
    scalarRestriction i U hU r q = X.presheaf.map ((TopologicalSpace.Opens.map i.base).map (AffinePrincipal.Sections.inclusion U r)).op q := by
  change (Affine.ChartSections.iso (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) (scalarSheaf i)).inv
    ((Affine.ChartSections.iso (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) (scalarSheaf i)).hom
      ((scalarSheaf i).presheaf.map (AffinePrincipal.Sections.inclusion U r).op
        ((Affine.ChartSections.iso U hU (scalarSheaf i)).inv
          ((Affine.ChartSections.iso U hU (scalarSheaf i)).hom q)))) = _
  rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]
  rfl

omit [IsFinite f] [IsClosedImmersion i] in
theorem coefficient_restriction (m : Finite.FlatCoefficientSections.coefficientRing f i U) :
    coefficientRestriction f i U hU r m =
      Y.presheaf.map ((TopologicalSpace.Opens.map f.base).map ((TopologicalSpace.Opens.map i.base).map (AffinePrincipal.Sections.inclusion U r))).op m := by
  change (Affine.ChartSections.iso (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) (coefficientSheaf f i)).inv
    ((Affine.ChartSections.iso (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) (coefficientSheaf f i)).hom
      ((coefficientSheaf f i).presheaf.map (AffinePrincipal.Sections.inclusion U r).op
        ((Affine.ChartSections.iso U hU (coefficientSheaf f i)).inv
          ((Affine.ChartSections.iso U hU (coefficientSheaf f i)).hom m)))) = _
  rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]
  rfl

omit [IsFinite f] [IsClosedImmersion i] in
theorem multiplication (q : Finite.FlatCoefficientSections.quotientRing i U) (m : Finite.FlatCoefficientSections.coefficientRing f i U) :
    coefficientRestriction f i U hU r (q • m) =
      scalarRestriction i U hU r q • coefficientRestriction f i U hU r m := by
  rw [scalar_restriction, coefficient_restriction, coefficient_restriction]
  change (Y.presheaf.map ((TopologicalSpace.Opens.map f.base).map ((TopologicalSpace.Opens.map i.base).map (AffinePrincipal.Sections.inclusion U r))).op).hom
      ((f.app (i ⁻¹ᵁ U)).hom q * m) =
    (f.app (i ⁻¹ᵁ AffinePrincipal.Sections.openSubset U r)).hom
        ((X.presheaf.map ((TopologicalSpace.Opens.map i.base).map (AffinePrincipal.Sections.inclusion U r)).op).hom q) *
      (Y.presheaf.map ((TopologicalSpace.Opens.map f.base).map ((TopologicalSpace.Opens.map i.base).map (AffinePrincipal.Sections.inclusion U r))).op).hom m
  rw [_root_.map_mul]
  have h := ConcreteCategory.congr_hom (f.naturality ((TopologicalSpace.Opens.map i.base).map (AffinePrincipal.Sections.inclusion U r)).op) q
  exact congrArg (· * (Y.presheaf.map
    ((TopologicalSpace.Opens.map f.base).map ((TopologicalSpace.Opens.map i.base).map (AffinePrincipal.Sections.inclusion U r))).op).hom m) h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.RestrictionNormalization
