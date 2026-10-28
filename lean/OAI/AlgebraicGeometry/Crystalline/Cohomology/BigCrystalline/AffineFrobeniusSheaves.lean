import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusFrames
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackSheafAugmentation

/-! # Affine Frobenius Sheaves -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSheaves.BigCrystallineAffineFrobeniusSheaves

noncomputable section

/-! # The actual geometric Frobenius map on the affine frame sheaf resolution -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (hp : p.Prime) (W A σ : Type u) [CommRing W] [CommRing A]
  (hA : (p : A) = 0) (J : Ideal W) (δ : DividedPowers J)
  (base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p hp A hA
local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "bF" => g ≫ base
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackSheafTransport.BigCrystallinePullbackSheafTransport.restriction p W A A J δ base φ
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackResolution.BigCrystallinePullbackResolution.restriction p W A A J δ base φ
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ bF
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ base
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := bF) a
local notation "α" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := base) a
local notation "β" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := bF) a
local notation "α'" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.augmentation p W A J δ base a
local notation "β'" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.augmentation p W A J δ bF a
local notation "s" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackAugmentation.BigCrystallinePullbackAugmentation.sourceIso p W A A J δ base φ

def complexMap : ((F).mapHomologicalComplex (.up ℕ)).obj
    (FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ base a) ⟶
      FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W A J δ bF a :=
  ((Functor.mapHomologicalComplexCompIso
      (PullbackSheafTransport.BigCrystallinePullbackSheafTransport.comparisonIso p W A A J δ base φ) (.up ℕ)).app K).hom ≫
    ((S).mapHomologicalComplex (.up ℕ)).map
      (AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames.complexMap p hp W A σ hA J δ base a)

theorem presheaf_zero : (P).map ((α).f 0) ≫
      (AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames.complexMap p hp W A σ hA J δ base a).f 0 =
    (s).hom ≫ (β).f 0 := by
  have h := congrArg (fun f => f.f 0)
    (AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames.augmentation p hp W A σ hA J δ base a)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at h
  have hm : (PullbackAugmentation.BigCrystallinePullbackAugmentation.augmentation p W A A σ J δ base φ a).f 0 =
      (P).map ((α).f 0) := Mapped.AugmentationZero.MappedAugmentationZero.mapped P α
  rw [hm] at h
  exact h

theorem augmentation : (F).map ((α').f 0) ≫
      (complexMap p hp W A σ hA J δ base a).f 0 =
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureTransport
      (p := p) (J := J) (δ := δ) (fY := base) g rfl).hom ≫ (β').f 0 := by
  have hα : (α').f 0 = (T).map ((α).f 0) :=
    (Mapped.AugmentationZero.MappedAugmentationZero.normalized T α
      (FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientIso p W A J δ base)).trans (Category.id_comp _)
  have hβ : (β').f 0 = (S).map ((β).f 0) :=
    (Mapped.AugmentationZero.MappedAugmentationZero.normalized S β
      (FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientIso p W A J δ bF)).trans (Category.id_comp _)
  rw [hα, hβ, ← PullbackSheafTransport.BigCrystallinePullbackSheafTransport.structureIso_original]
  let G₀ := NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) base
  let H₀ := NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) bF
  let b : G₀ ⟶ (K).X 0 := (α).f 0
  let v : (P).obj ((K).X 0) ⟶ (L).X 0 :=
    (AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames.complexMap p hp W A σ hA J δ base a).f 0
  let w : (P).obj G₀ ⟶ H₀ := (s).hom
  let z : H₀ ⟶ (L).X 0 := (β).f 0
  let i := PullbackSheafTransport.BigCrystallinePullbackSheafTransport.comparisonIso p W A A J δ base φ
  have hc : (F).map ((T).map b) ≫ i.hom.app ((K).X 0) = i.hom.app G₀ ≫ (S).map ((P).map b) :=
    i.hom.naturality b
  have hp₀ : (P).map b ≫ v = w ≫ z := presheaf_zero p hp W A σ hA J δ base a
  have hv : (S).map ((P).map b) ≫ (S).map v = (S).map w ≫ (S).map z :=
    ((S).map_comp ((P).map b) v).symm.trans ((congrArg (S).map hp₀).trans ((S).map_comp w z))
  change (F).map ((T).map b) ≫ (i.hom.app ((K).X 0) ≫ (S).map v) =
    (i.hom.app G₀ ≫ (S).map w) ≫ (S).map z
  rw [← Category.assoc, hc, Category.assoc, hv, ← Category.assoc]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusSheaves.BigCrystallineAffineFrobeniusSheaves
