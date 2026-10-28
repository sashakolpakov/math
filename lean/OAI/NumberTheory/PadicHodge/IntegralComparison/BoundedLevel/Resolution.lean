import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransport

/-! # Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Resolution

noncomputable section

/-! A common original crystalline injective resolution restricts compatibly to both bounded levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))

local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm
local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f n I
local notation "Im" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f m I

def cocomplexIso : ((T).mapHomologicalComplex (ComplexShape.up ℕ)).obj (Im).cocomplex ≅ (In).cocomplex :=
  Iso.refl _

theorem augmentation_zero :
    (Single.ComplexTransport.map T (Bounded.CohomologyTransition.structureIso f n m hnm) (Im).ι).f 0 ≫
      (cocomplexIso f n m hnm I).hom.f 0 = (In).ι.f 0 := by
  have h := Single.ComplexTransport.map_zero T (Bounded.CohomologyTransition.structureIso f n m hnm) (Im).ι
  have hm := ExactInjectiveResolution.map_ι_zero (BoundedCrystalline.Site.restriction f m) I
  have hn := ExactInjectiveResolution.map_ι_zero (BoundedCrystalline.Site.restriction f n) I
  change (Single.ComplexTransport.map T (Bounded.CohomologyTransition.structureIso f n m hnm) (Im).ι).f 0 ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact h.trans ((Category.id_comp _).trans ((congrArg (T).map hm).trans hn.symm))

theorem augmentation :
    Single.ComplexTransport.map T (Bounded.CohomologyTransition.structureIso f n m hnm) (Im).ι ≫
      (cocomplexIso f n m hnm I).hom = (In).ι := by
  apply (CochainComplex.fromSingle₀Equiv (In).cocomplex
    (BoundedCrystalline.CrystallineCohomology.structureSheaf f n)).injective
  apply Subtype.ext
  exact augmentation_zero f n m hnm I

theorem augmentation_eq :
    Single.ComplexTransport.map T (Bounded.CohomologyTransition.structureIso f n m hnm) (Im).ι = (In).ι := by
  have h := augmentation f n m hnm I
  change Single.ComplexTransport.map T (Bounded.CohomologyTransition.structureIso f n m hnm) (Im).ι ≫ 𝟙 _ = _ at h
  simpa only [Category.comp_id] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Resolution
