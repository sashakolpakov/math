import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.InjectiveRestrictionSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution

/-! # Resolution Section Surjectivity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionSectionSurjectivity

noncomputable section

/-!
# IntegralComparison: the actual bounded resolution-section transitions are surjective
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution.Comparison.resolution (p := p) (J := J) (δ := δ) f
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.property (p := p) (J := J) (δ := δ) f

theorem global_restriction_surjective (i n : ℕ) : Function.Surjective
    (fun a => ExhaustivePresheafSections.restrictGlobal P (ModuleCat.of R R) ((I).cocomplex.X i).obj a n) := by
  let : Injective ((I).cocomplex.X i) := (I).injective i
  exact Sheaf.InjectiveRestrictionSections.restriction_surjective R BigCrystallineSite.Object.topology
    (ModuleCat.of R R) (P n) (fun α h => BoundedCrystalline.Site.property_of_hom f n α h) ((I).cocomplex.X i)

theorem transition_surjective (i n m : ℕ) (hnm : n ≤ m) : Function.Surjective
    (ExhaustivePresheafSections.restrict P (BoundedSection.Reconstruction.monotone_property f)
      (ModuleCat.of R R) ((I).cocomplex.X i).obj n m hnm) := by
  intro a
  obtain ⟨b, hb⟩ := global_restriction_surjective (p := p) (J := J) (δ := δ) f i n a
  exact ⟨ExhaustivePresheafSections.restrictGlobal P (ModuleCat.of R R) ((I).cocomplex.X i).obj b m,
    ((ExhaustivePresheafSections.restrictGlobal_compatible P (BoundedSection.Reconstruction.monotone_property f)
      (ModuleCat.of R R) ((I).cocomplex.X i).obj b) n m hnm).trans hb⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionSectionSurjectivity
