import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Continuous
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RingDescent

/-! # Principal Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.PrincipalSections

noncomputable section

/-!
# IntegralComparison: crystalline principal sections are affine Zariski sections

The divided-power localization ring is canonically the ring of sections
on the corresponding principal open of the ambient affine scheme. These
isomorphisms commute with every principal-open restriction map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens.Category (Principal toOpens)
open OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Functor

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (U : BigCrystallineSite.Object p B J δ f)

abbrev Sections (r : PrincipalOpens.Category.Principal U.ring) :=
  (Spec.structureSheaf U.ring).obj.obj (op (PrimeSpectrum.basicOpen r.function))

instance sectionsAlgebra (r : PrincipalOpens.Category.Principal U.ring) : Algebra U.ring (Sections U r) :=
  StructureSheaf.openAlgebra U.ring _

instance sectionsLocalization (r : PrincipalOpens.Category.Principal U.ring) : IsLocalization.Away r.function (Sections U r) :=
  StructureSheaf.IsLocalization.to_basicOpen U.ring r.function

def sectionsEquiv (r : PrincipalOpens.Category.Principal U.ring) : Crystalline.Localization.Ring U r.function ≃ₐ[U.ring] Sections U r :=
  IsLocalization.algEquiv (Submonoid.powers r.function) _ _

def ringPresheaf : (PrincipalOpens.Category.Principal U.ring)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.inclusion U).op ⋙ (Over.forget U).op ⋙ Crystalline.RingDescent.ringPresheaf f

def zariskiPresheaf : (PrincipalOpens.Category.Principal U.ring)ᵒᵖ ⥤ CommRingCat.{u} :=
  (PrincipalOpens.Category.toOpens U.ring).op ⋙ (Spec.structureSheaf U.ring).obj

theorem sections_natural {r s : PrincipalOpens.Category.Principal U.ring} (a : r ⟶ s) :
    (ringPresheaf U).map a.op ≫ (sectionsEquiv U r).toRingEquiv.toCommRingCatIso.hom =
      (sectionsEquiv U s).toRingEquiv.toCommRingCatIso.hom ≫ (zariskiPresheaf U).map a.op := by
  apply CommRingCat.hom_ext
  change (sectionsEquiv U r).toRingHom.comp ((Functor.inclusion U).map a).left.ringMap.toRingHom =
    ((Spec.structureSheaf U.ring).obj.map ((PrincipalOpens.Category.toOpens U.ring).map a).op).hom.comp
      (sectionsEquiv U s).toRingHom
  apply IsLocalization.ringHom_ext (S := Crystalline.Localization.Ring U s.function) (Submonoid.powers s.function)
  apply RingHom.ext
  intro x
  have h := congrArg (fun g => g.ringMap x) (Over.w ((Functor.inclusion U).map a))
  change (sectionsEquiv U r) (((Functor.inclusion U).map a).left.ringMap
      (algebraMap U.ring (Crystalline.Localization.Ring U s.function) x)) =
    ((Spec.structureSheaf U.ring).obj.map ((PrincipalOpens.Category.toOpens U.ring).map a).op)
      ((sectionsEquiv U s) (algebraMap U.ring (Crystalline.Localization.Ring U s.function) x))
  change ((Functor.inclusion U).map a).left.ringMap (algebraMap U.ring (Crystalline.Localization.Ring U s.function) x) =
    algebraMap U.ring (Crystalline.Localization.Ring U r.function) x at h
  rw [h, (sectionsEquiv U r).commutes, (sectionsEquiv U s).commutes]
  rfl

theorem sections_natural_apply {r s : PrincipalOpens.Category.Principal U.ring} (a : r ⟶ s) (x : Crystalline.Localization.Ring U s.function) :
    sectionsEquiv U r (((Functor.inclusion U).map a).left.ringMap x) =
      (zariskiPresheaf U).map a.op (sectionsEquiv U s x) := by
  have h := congrArg (fun g => g.hom) (sections_natural U a)
  exact DFunLike.congr_fun h x

def ringPresheafIso : ringPresheaf U ≅ zariskiPresheaf U :=
  NatIso.ofComponents (fun r => (sectionsEquiv U r.unop).toRingEquiv.toCommRingCatIso)
    (fun a => sections_natural U a.unop)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.PrincipalSections
