import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.OpenCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex

/-! # Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Resolution

noncomputable section

/-!
# IntegralComparison: a global bounded injective resolution computes the original chart cohomology
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (g : X ⟶ Y) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))

def resolution : InjectiveResolution
    (Sheaves.structureSheaf (p := p) (J := J) (δ := δ) fY g n) :=
  ExactInjectiveResolution.map (Subsite.restriction fY g n) I

def complex : CochainComplex (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ :=
  Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2}
    (Crystalline.ExactRestriction.Coeff (B := B)) (Subsite.topology fY g n) (resolution fY g n I).cocomplex

def subsiteHomologyIso (i : ℕ) : (complex fY g n I).homology i ≅
    ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B))
      (OpenCohomology.Cohomology (p := p) (J := J) (δ := δ) fY g n i) :=
  Sheaf.PresheafSectionComplex.homologyIso.{u + 1, u, u + 1, u + 2}
    (Crystalline.ExactRestriction.Coeff (B := B)) (Subsite.topology fY g n) (resolution fY g n I) i

variable {fY} {f : X ⟶ Spec (CommRingCat.of B)} [Mono g] (hg : g ≫ fY = f)

def homologyIso (i : ℕ) : (complex fY g n I).homology i ≅
    ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B))
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) :=
  subsiteHomologyIso fY g n I i ≪≫
    (OpenCohomology.cohomologyEquiv g n hg i).toModuleIso

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Resolution
