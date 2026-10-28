import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafInjectives
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex

/-! # Geometric Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution

noncomputable section

/-!
# IntegralComparison: the actual global injective resolution restricts to the original chart structure sheaf
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

instance restriction_preservesInjectives : (R).PreservesInjectiveObjects := by
  change (BoundedOpen.Subsite.restriction fY g n ⋙
    (BoundedOpen.Sheaves.equivalence g hg n).functor).PreservesInjectiveObjects
  infer_instance

variable (I : InjectiveResolution
  (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) fY n))

def resolution : InjectiveResolution
    (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n) where
  cocomplex := ((R).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective i := (R).injective_obj_of_injective (I.injective i)
  ι := Single.ComplexTransport.map R (BoundedOpen.Sheaves.structureTransport g hg n) I.ι
  quasiIso := by
    dsimp only [Single.ComplexTransport.map]
    infer_instance

theorem augmentation_zero : (resolution g hg n I).ι.f 0 =
    (BoundedOpen.Sheaves.structureTransport g hg n).inv ≫ (R).map (I.ι.f 0) :=
  Single.ComplexTransport.map_zero R (BoundedOpen.Sheaves.structureTransport g hg n) I.ι

def complex : CochainComplex (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ :=
  Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2}
    (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n) (resolution g hg n I).cocomplex

def homologyIso (i : ℕ) : (complex g hg n I).homology i ≅
    ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B))
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) :=
  Sheaf.PresheafSectionComplex.homologyIso.{u + 1, u, u + 1, u + 2}
    (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n) (resolution g hg n I) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution
