import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerAugmentation
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Affine

/-! # Affine Frobenius Frames -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames

noncomputable section

/-! # The actual affine Frobenius map of big crystalline frame resolutions -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (hp : p.Prime) (W A σ : Type u) [CommRing W] [CommRing A]
  (hA : (p : A) = 0) (J : Ideal W) (δ : DividedPowers J)
  (base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p hp A hA
local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "bF" => g ≫ base
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackResolution.BigCrystallinePullbackResolution.restriction p W A A J δ base φ

omit [Fintype σ] [LinearOrder σ] in
theorem geometric_map : g = Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp (Spec (CommRingCat.of A))
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p A hA) :=
  (Picard.Homomorphisms.Affine.Construction.absoluteFrobenius_spec p hp A hA).symm

def complexMap : ((F).mapHomologicalComplex (.up ℕ)).obj
    (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a) ⟶
      FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := bF) a :=
  (PullbackResolution.BigCrystallinePullbackResolution.iso p W A A σ J δ base φ a).hom ≫
    PowerForms.BigCrystallinePowerForms.complexMap (p := p) (J := J) (δ := δ) (base := bF) a p

theorem augmentation : PullbackAugmentation.BigCrystallinePullbackAugmentation.augmentation p W A A σ J δ base φ a ≫
      complexMap p hp W A σ hA J δ base a =
    (CochainComplex.single₀ _).map (PullbackAugmentation.BigCrystallinePullbackAugmentation.sourceIso p W A A J δ base φ).hom ≫
      FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := bF) a := by
  let f : FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := bF) (φ ∘ a) ⟶
      FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := bF) a :=
    PowerForms.BigCrystallinePowerForms.complexMap (p := p) (J := J) (δ := δ) (base := bF) a p
  have hf : FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := bF) (φ ∘ a) ≫ f =
      FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := bF) a :=
    PowerAugmentation.BigCrystallinePowerAugmentation.original (p := p) (J := J) (δ := δ) (base := bF) a p
  change PullbackAugmentation.BigCrystallinePullbackAugmentation.augmentation p W A A σ J δ base φ a ≫
    ((PullbackResolution.BigCrystallinePullbackResolution.iso p W A A σ J δ base φ a).hom ≫ f) = _
  rw [← Category.assoc, PullbackAugmentation.BigCrystallinePullbackAugmentation.square, Category.assoc, hf]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames
