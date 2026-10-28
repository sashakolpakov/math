import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex

/-! # Bounded Resolution Levels -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolutionLevels

noncomputable section

/-!
# IntegralComparison: the reconstructed original resolution maps to each actual bounded level
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution.Comparison.resolution (p := p) (J := J) (δ := δ) f
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution.Comparison.complex (p := p) (J := J) (δ := δ) f

def resolution : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n) :=
  BoundedCrystalline.CrystallineCohomology.resolution f n I

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R
    (BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n) (resolution f n).cocomplex

def homologyIso (i : ℕ) : (complex (p := p) (J := J) (δ := δ) f n).homology i ≅
    ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) :=
  Sheaf.PresheafSectionComplex.homologyIso.{u + 1, u, u + 1, u + 2} R (BoundedCrystalline.Site.topology f n) (resolution f n) i

def projection : G ⟶ complex (p := p) (J := J) (δ := δ) f n where
  f i := ModuleCat.ofHom (X := (G).X i) (Y := (complex (p := p) (J := J) (δ := δ) f n).X i)
    { toFun := fun x => ULift.up (x.down.val n)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm' _ _ _ := ModuleCat.hom_ext (LinearMap.ext (fun _ => rfl))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolutionLevels
