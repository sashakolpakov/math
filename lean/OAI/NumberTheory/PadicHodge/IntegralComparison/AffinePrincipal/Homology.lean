import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.PrincipalComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyPreservationCompose
import OAI.NumberTheory.PadicHodge.IntegralComparison.MapHomologyIsoCompose
import OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtensionExact
import Mathlib.RingTheory.Flat.Localization

/-! # Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Homology

noncomputable section

/-! Principal restriction as an actual natural transformation of section
functors, retaining the scalar action on every original sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections

private theorem tensor_ext {R S M T : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup T] [Module S T]
    {f g : S ⊗[R] M →ₗ[S] T} (h : ∀ a m, f (a ⊗ₜ[R] m) = g (a ⊗ₜ[R] m)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a m => exact h a m

variable {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U))

local instance sectionModule (M : X.Modules) : Module Γ(X, U) Γ(M, Sections.openSubset U r) :=
  Module.compHom _ (algebraMap Γ(X, U) Γ(X, Sections.openSubset U r))

local instance sectionTower (M : X.Modules) :
    IsScalarTower Γ(X, U) Γ(X, Sections.openSubset U r) Γ(M, Sections.openSubset U r) where
  smul_assoc a b m := by
    change (algebraMap Γ(X, U) Γ(X, Sections.openSubset U r) a * b) • m =
      algebraMap Γ(X, U) Γ(X, Sections.openSubset U r) a • (b • m)
    exact mul_smul _ _ _

def component (M : X.Modules) :
    Γ(X, Sections.openSubset U r) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, Sections.openSubset U r)] Γ(M, Sections.openSubset U r) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : Γ(X, Sections.openSubset U r) →ₗ[Γ(X, Sections.openSubset U r)] Γ(X, Sections.openSubset U r)).smulRight
      (Sections.restriction U r M))

theorem component_tmul (M : X.Modules) (a : Γ(X, Sections.openSubset U r)) (m : Γ(M, U)) :
    component U r M (a ⊗ₜ[Γ(X, U)] m) = a • M.presheaf.map (Sections.inclusion U r).op m := rfl

abbrev tensorFunctor := PrincipalComplex.tensorFunctor U r

def restriction : Affine.ModuleExactSections.sections U ⋙ tensorFunctor U r ⟶
    Affine.ModuleExactSections.sections (Sections.openSubset U r) where
  app M := ModuleCat.ofHom (component U r M)
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply tensor_ext
    intro a m
    change component U r N (a ⊗ₜ[Γ(X, U)] f.val.app (op U) m) =
      f.val.app (op (Sections.openSubset U r)) (component U r M (a ⊗ₜ[Γ(X, U)] m))
    rw [component_tmul, component_tmul, map_smul]
    exact congrArg (fun z => a • z)
      (PresheafOfModules.naturality_apply f.val (Sections.inclusion U r).op m).symm

theorem restriction_eq_iso (hU : IsAffineOpen U) (M : X.Modules) [M.IsQuasicoherent] :
    (restriction U r).app M = (Sections.iso U hU r M).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply tensor_ext
  intro a m
  rfl

theorem complex_restriction (hU : IsAffineOpen U) (K : CochainComplex X.Modules ℕ)
    [∀ i, (K.X i).IsQuasicoherent] :
    ((restriction U r).mapHomologicalComplex (.up ℕ)).app K =
      (PrincipalComplex.iso U hU r (.up ℕ) K).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact restriction_eq_iso U r hU (K.X i)

def tensorHomologyIso (hU : IsAffineOpen U) (T : ShortComplex (ModuleCat Γ(X, U))) :
    (T.map (tensorFunctor U r)).homology ≅ (tensorFunctor U r).obj T.homology := by
  letI : IsLocalization.Away r Γ(X, Sections.openSubset U r) := hU.isLocalization_basicOpen r
  letI : Module.Flat Γ(X, U) Γ(X, Sections.openSubset U r) :=
    IsLocalization.flat Γ(X, Sections.openSubset U r) (Submonoid.powers r)
  exact T.mapHomologyIso (tensorFunctor U r)

theorem homology_naturality (hU : IsAffineOpen U) (T : ShortComplex X.Modules)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent] :
    (tensorFunctor U r).map (Affine.ModuleHomology.iso U hU T).inv ≫
        (tensorHomologyIso U r hU (T.map (Affine.ModuleExactSections.sections U))).inv ≫
          ShortComplex.homologyMap (T.mapNatTrans (restriction U r)) =
      (restriction U r).app T.homology ≫
        (Affine.ModuleHomology.iso (Sections.openSubset U r) (hU.basicOpen r) T).inv := by
  let : IsLocalization.Away r Γ(X, Sections.openSubset U r) := hU.isLocalization_basicOpen r
  let : Module.Flat Γ(X, U) Γ(X, Sections.openSubset U r) :=
    IsLocalization.flat Γ(X, Sections.openSubset U r) (Submonoid.powers r)
  let := Affine.ModuleHomology.preservesLeft U hU T
  let := Affine.ModuleHomology.preservesRight U hU T
  let := Affine.ModuleHomology.preservesLeft (Sections.openSubset U r) (hU.basicOpen r) T
  let := Affine.ModuleHomology.preservesRight (Sections.openSubset U r) (hU.basicOpen r) T
  let := HomologyPreservationCompose.left (Affine.ModuleExactSections.sections U)
    (tensorFunctor U r) T
  let := HomologyPreservationCompose.right (Affine.ModuleExactSections.sections U)
    (tensorFunctor U r) T
  change (tensorFunctor U r).map (T.mapHomologyIso (Affine.ModuleExactSections.sections U)).inv ≫
      ((T.map (Affine.ModuleExactSections.sections U)).mapHomologyIso (tensorFunctor U r)).inv ≫
        ShortComplex.homologyMap (T.mapNatTrans (restriction U r)) =
    (restriction U r).app T.homology ≫
      (T.mapHomologyIso (Affine.ModuleExactSections.sections (Sections.openSubset U r))).inv
  rw [← Category.assoc, ← MapHomologyIsoCompose.inv_comp,
    ShortComplex.homologyMap_mapNatTrans, ← Category.assoc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Homology
