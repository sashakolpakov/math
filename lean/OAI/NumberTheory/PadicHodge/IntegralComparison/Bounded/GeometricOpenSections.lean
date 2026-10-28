import OAI.NumberTheory.PadicHodge.IntegralComparison.EquivalentPresheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Resolution

/-! # Geometric Open Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricOpenSections

noncomputable section

/-!
# IntegralComparison: the geometric chart section complex is the original incoming-subsite section complex
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) fY g n
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

def linearEquiv (F : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n) :
    ((Functor.const (BoundedOpen.Subsite.Objects (p := p) (J := J) (δ := δ) fY g n)ᵒᵖ).obj
      (ModuleCat.of R R) ⟶ ((S).obj F).obj) ≃ₗ[R]
    ((Functor.const (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ).obj
      (ModuleCat.of R R) ⟶ ((G).obj F).obj) :=
  EquivalentPresheafSections.linearEquiv R (BoundedOpen.Equivalence.openFunctor g hg n)
    (ModuleCat.of R R) ((S).obj F).obj

theorem naturality {F H : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n}
    (a : (Functor.const (BoundedOpen.Subsite.Objects (p := p) (J := J) (δ := δ) fY g n)ᵒᵖ).obj
      (ModuleCat.of R R) ⟶ ((S).obj F).obj) (b : F ⟶ H) :
    linearEquiv g hg n H (a ≫ ((S).map b).hom) = linearEquiv g hg n F a ≫ ((G).map b).hom := rfl

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
  (p := p) (J := J) (δ := δ) fY n))

def complexIso : BoundedOpen.Resolution.complex fY g n I ≅ GeometricResolution.complex g hg n I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapIso
      (linearEquiv g hg n (I.cocomplex.X i)).toModuleIso)
    (by
      intro i j hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricOpenSections
