import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafInjectives

/-! # Injective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Injective.Comparison

noncomputable section

/-!
# IntegralComparison: an actual bounded frame resolution compares to any injective resolution of the original sheaf
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) f n))
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation f n F)]

local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n F
local notation "ι" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.augmentation f n F

def map : K ⟶ I.cocomplex := Augmented.ResolutionToInjective.map K ι I (𝟙 _)

theorem augmentation : ι ≫ map f n F I = I.ι :=
  (Augmented.ResolutionToInjective.augmentation K ι I (𝟙 _)).trans
    ((congrArg (fun a => a ≫ I.ι) ((CochainComplex.single₀ _).map_id _)).trans (Category.id_comp _))

instance map_quasiIso : QuasiIso (map f n F I) := Augmented.ResolutionToInjective.quasiIso K ι I (𝟙 _)

def homotopy (a : K ⟶ I.cocomplex) (ha : ι ≫ a = I.ι) : Homotopy (map f n F I) a :=
  Augmented.ResolutionHomotopy.homotopy K ι I (map f n F I) a ((augmentation f n F I).trans ha.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Injective.Comparison
