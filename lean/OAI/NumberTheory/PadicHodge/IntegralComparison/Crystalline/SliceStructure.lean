import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Constant
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureDescent

/-! # Slice Structure -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceStructure

noncomputable section

/-!
# IntegralComparison: principal-open cohomology of the original crystalline structure sheaf

The slice coefficient is the restriction of the original crystalline
structure sheaf. Its principal-open restriction is identified with the
actual ambient-ring presheaf by the canonical sheafification isomorphism.
The resulting cohomology equivalence has no acyclicity assumption.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Functor OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Extension
open OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Constant.Comparison (constantUnit principalConstantUnit)

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (U : BigCrystallineSite.Object p B J δ f)

abbrev structureSheaf : CrystallinePrincipal.Extension.SliceSheaf U :=
  (BigCrystallineSite.Object.topology.overPullback (ModuleCat.{u + 1} (CrystallinePrincipal.Extension.Coeff (B := B))) U).obj
    (BigCrystallineCohomology.structureSheaf f)

def principalPresheaf : (PrincipalOpens.Category.Principal U.ring)ᵒᵖ ⥤
    ModuleCat.{u + 1} (CrystallinePrincipal.Extension.Coeff (B := B)) :=
  (CrystallinePrincipal.Functor.inclusion U).op ⋙ (Over.forget U).op ⋙ BigCrystallineCohomology.largePresheaf f

def structurePresheafIso : principalPresheaf U ≅ ((CrystallinePrincipal.Extension.restriction U).obj (structureSheaf U)).obj :=
  Functor.isoWhiskerLeft (CrystallinePrincipal.Functor.inclusion U).op
    (Functor.isoWhiskerLeft (Over.forget U).op (StructureDescent.structurePresheafIso f))

theorem principalPresheaf_isSheaf :
    Presheaf.IsSheaf (Principal.Topology.topology U.ring) (principalPresheaf U) :=
  (Presheaf.isSheaf_of_iso_iff (structurePresheafIso U)).mpr
    ((CrystallinePrincipal.Extension.restriction U).obj (structureSheaf U)).property

def principalStructureSheaf : CrystallinePrincipal.Extension.PrincipalSheaf U := ⟨principalPresheaf U, principalPresheaf_isSheaf U⟩

def structureTransport : (CrystallinePrincipal.Extension.restriction U).obj (structureSheaf U) ≅ principalStructureSheaf U :=
  ObjectProperty.isoMk _ (structurePresheafIso U).symm

abbrev Cohomology (n : ℕ) := Abelian.Ext.{u + 2} (CrystallinePrincipal.Constant.Comparison.constantUnit U) (structureSheaf U) n

abbrev PrincipalCohomology (n : ℕ) :=
  Abelian.Ext.{u + 2} (CrystallinePrincipal.Constant.Comparison.principalConstantUnit U) (principalStructureSheaf U) n

def comparison (n : ℕ) : Cohomology U n →ₗ[CrystallinePrincipal.Extension.Coeff (B := B)] PrincipalCohomology U n :=
  (Etale.Frobenius.extIsoCongr (CrystallinePrincipal.Extension.Coeff (B := B)) (Iso.refl _) (structureTransport U) n).toLinearMap.comp
    (CrystallinePrincipal.Constant.Comparison.comparison U (structureSheaf U) n)

theorem comparison_bijective (n : ℕ) : Function.Bijective (comparison U n) :=
  (Etale.Frobenius.extIsoCongr (CrystallinePrincipal.Extension.Coeff (B := B)) (Iso.refl _) (structureTransport U) n).bijective.comp
    (CrystallinePrincipal.Constant.Comparison.comparison_bijective U (structureSheaf U) n)

def cohomologyEquiv (n : ℕ) : Cohomology U n ≃ₗ[CrystallinePrincipal.Extension.Coeff (B := B)] PrincipalCohomology U n :=
  LinearEquiv.ofBijective (comparison U n) (comparison_bijective U n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceStructure
