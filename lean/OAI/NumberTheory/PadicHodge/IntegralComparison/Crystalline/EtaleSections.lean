import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleLift

/-! # Etale Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleSections

noncomputable section

/-! Étale affine factors give actual sections and degree-zero classes of the original crystalline structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConstantSections OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleLift

attribute [local instance] EtaleResidue.objectAlgebra

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  (A : Type u) [CommRing A] [Algebra B A] [Algebra.Etale B A]
  (g : X ⟶ Spec (CommRingCat.of A))
  (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap B A)) = f)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.largePresheaf (p := p) (J := J) (δ := δ) f

abbrev source : ModuleCat.{u + 1} R :=
  (ModuleCat.restrictScalars (ULift.ringEquiv : R ≃+* B).toRingHom).obj
    ((ModuleCat.uliftFunctor.{u + 1} B).obj (ModuleCat.of B A))

def sectionOf (a : A) : ConstantSections.Sections (p := p) (J := J) (δ := δ) f where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton R ((P).obj U)
    (ULift.up (EtaleLift.lift A g hg U.unop a)))
  naturality {U V} α := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    apply ULift.ext
    change V.unop.base 1 * EtaleLift.lift A g hg V.unop a =
      α.unop.ringMap (U.unop.base 1 * EtaleLift.lift A g hg U.unop a)
    rw [map_one, map_one, one_mul, one_mul]
    exact (AlgHom.congr_fun (EtaleLift.natural A g hg α.unop) a).symm

theorem value_sectionOf (a : A) (U : BigCrystallineSite.Object p B J δ f) :
    ConstantSections.value f (sectionOf A g hg a) U = EtaleLift.lift A g hg U a := by
  change U.base 1 * EtaleLift.lift A g hg U a = _
  rw [map_one, one_mul]

def sectionsMap : source (B := B) A →ₗ[R] ConstantSections.Sections (p := p) (J := J) (δ := δ) f where
  toFun a := sectionOf A g hg a.down
  map_add' a b := by
    apply ConstantSections.ext f
    intro U
    change ConstantSections.value f (sectionOf A g hg (a.down + b.down)) U =
      ConstantSections.value f (sectionOf A g hg a.down) U + ConstantSections.value f (sectionOf A g hg b.down) U
    rw [value_sectionOf, value_sectionOf, value_sectionOf, map_add]
  map_smul' r a := by
    apply ConstantSections.ext f
    intro U
    change ConstantSections.value f (sectionOf A g hg (r.down • a.down)) U =
      U.base r.down * ConstantSections.value f (sectionOf A g hg a.down) U
    rw [value_sectionOf, value_sectionOf]
    exact (EtaleLift.lift A g hg U).toLinearMap.map_smul r.down a.down

def cohomologyMap : source (B := B) A →ₗ[R]
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f 0 :=
  (ConstantSections.cohomologyEquiv f).symm.toLinearMap.comp (sectionsMap A g hg)

def baseCohomologyMap : A →ₗ[B]
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f 0 where
  toFun a := cohomologyMap A g hg (ULift.up a)
  map_add' a b := (cohomologyMap A g hg).map_add (ULift.up a) (ULift.up b)
  map_smul' b a := (cohomologyMap A g hg).map_smul (ULift.up b : R) (ULift.up a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleSections
