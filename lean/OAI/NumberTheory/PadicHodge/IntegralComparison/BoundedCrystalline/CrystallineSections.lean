import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConstantSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTorsion

/-! # Crystalline Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineSections

noncomputable section

/-! Values and constant sections in the original bounded crystalline degree-zero cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

abbrev presheaf := (Site.inclusion (p := p) (J := J) (δ := δ) f n).op ⋙
  BigCrystallineCohomology.largePresheaf f

abbrev Sections :=
  ((Functor.const (Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ).obj
    (ModuleCat.of R R) ⟶ presheaf f n)

def value (s : Sections (p := p) (J := J) (δ := δ) f n)
    (U : Site.Objects (p := p) (J := J) (δ := δ) f n) : U.obj.ring :=
  (s.app (op U) (1 : R)).down

theorem value_natural (s : Sections (p := p) (J := J) (δ := δ) f n)
    {U V : Site.Objects (p := p) (J := J) (δ := δ) f n} (g : U ⟶ V) :
    g.hom.ringMap (value f n s V) = value f n s U := by
  exact (congrArg (fun a => (a (1 : R)).down) (s.naturality g.op)).symm

def restriction : Crystalline.ConstantSections.Sections (p := p) (J := J) (δ := δ) f →ₗ[R]
    Sections (p := p) (J := J) (δ := δ) f n where
  toFun s := Functor.whiskerLeft (Site.inclusion f n).op s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def constants : R →ₗ[R] Sections (p := p) (J := J) (δ := δ) f n :=
  (restriction f n).comp (Crystalline.ConstantSections.constants f)

theorem value_constants (w : R)
    (U : Site.Objects (p := p) (J := J) (δ := δ) f n) :
    value f n (constants f n w) U = U.obj.base w.down :=
  Crystalline.ConstantSections.value_constants f w U.obj

theorem ext (s t : Sections (p := p) (J := J) (δ := δ) f n)
    (h : ∀ U, value f n s U = value f n t U) : s = t := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  apply ULift.ext
  exact h U.unop

def evaluation (U : Site.Objects (p := p) (J := J) (δ := δ) f n) :
    Sections (p := p) (J := J) (δ := δ) f n →ₗ[R] (presheaf (p := p) (J := J) (δ := δ) f n).obj (op U) where
  toFun s := s.app (op U) (1 : R)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cohomologyEquiv : CrystallineCohomology.Cohomology
    (p := p) (J := J) (δ := δ) f n 0 ≃ₗ[R] Sections (p := p) (J := J) (δ := δ) f n :=
  Abelian.Ext.linearEquiv₀.trans
    ((LinearAdjunction.homLinearEquiv R
      (sheafificationAdjunction (Site.topology f n) (ModuleCat.{u + 1} R))
      ((Functor.const (Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ).obj
        (ModuleCat.of R R)) (CrystallineCohomology.structureSheaf f n)).trans
      (Linear.homCongr R (Iso.refl _) (Bounded.CohomologyTorsion.structurePresheafIso f n).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineSections
