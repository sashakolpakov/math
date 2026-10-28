import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrameUniversal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category

/-! # Levels -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Levels.FramedPolynomialLevels

noncomputable section

/-!
# Actual polynomial envelope levels with their frame coordinates

The p-power PD-envelope tower of a surjective polynomial Witt presentation
has canonical lifted coordinates. Every framed crystalline object killed
by the corresponding power of p maps into that level, preserving those
specified coordinates and the actual residual open immersion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "A" => MvPolynomial σ W
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B

def base (n : ℕ) : Site.Object p k X :=
  AffineFrameCover.CrystallineAffineFrameCover.frame p k B A r hr hbase n

theorem residualMap_base (n : ℕ) (b : B) :
    AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B (FramedPolynomialLevels.base p k B σ r hr hbase n) b = b := by
  change (Spec.preimage (𝟙 (Spec (CommRingCat.of B)))).hom b = b
  rw [Spec.preimage_id]
  rfl

def level (n : ℕ) : FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a where
  base := FramedPolynomialLevels.base p k B σ r hr hbase n
  coordinate i := Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B A r hr hbase n (MvPolynomial.X i)
  reduction_coordinate i :=
    (Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient_reduction p k B A r hr hbase n (MvPolynomial.X i)).trans
      (residualMap_base p k B σ r hr hbase n (r (MvPolynomial.X i))).symm

variable (P : FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ (fun i => r (MvPolynomial.X i)))

def polynomialLift : A →ₐ[W] P.base.thickening.ring := MvPolynomial.aeval P.coordinate

include hbase in
theorem polynomialLift_reduction : P.base.thickening.reduction.comp (polynomialLift p k B σ r P).toRingHom =
    (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P.base).toRingHom.comp r := by
  apply MvPolynomial.ringHom_ext
  · intro w
    change P.base.thickening.reduction (MvPolynomial.aeval P.coordinate (MvPolynomial.C w)) =
      AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P.base (r (MvPolynomial.C w))
    rw [MvPolynomial.aeval_C]
    have hb := DFunLike.congr_fun hbase w
    change r (MvPolynomial.C w) = algebraMap k B (WittVector.constantCoeff w) at hb
    rw [hb, AlgHom.commutes]
    exact DFunLike.congr_fun P.base.thickening.reduction_base w
  · intro i
    change P.base.thickening.reduction (MvPolynomial.aeval P.coordinate (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
    exact P.reduction_coordinate i

def map (n : ℕ) (hn : (p : P.base.thickening.ring) ^ (n + 1) = 0) :
    P ⟶ level p k B σ r hr hbase n where
  hom :=
    { reducedMap := AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P.base
      ambientMap := Affine.EnvelopeFrames.AffineEnvelopeFrames.frameMap p k B A r hr hbase P.base.residueRing P.base.thickening
        (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P.base) (polynomialLift p k B σ r P)
        (polynomialLift_reduction p k B σ r hbase P) n hn
      reduction_comm x := DFunLike.congr_fun
        (Affine.EnvelopeFrames.AffineEnvelopeFrames.frameMap_reduction p k B A r hr hbase P.base.residueRing P.base.thickening
          (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P.base) (polynomialLift p k B σ r P)
          (polynomialLift_reduction p k B σ r hbase P) n hn) x
      over_X := by
        change Spec.map (CommRingCat.ofHom (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P.base).toRingHom) ≫ 𝟙 _ = _
        rw [Category.comp_id]
        exact AffineFrameCover.CrystallineAffineFrameCover.residualMap_spec p k B P.base
      dp_comp := Affine.EnvelopeFrames.AffineEnvelopeFrames.frameMap_isDPMorphism p k B A r hr hbase P.base.residueRing P.base.thickening
        (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P.base) (polynomialLift p k B σ r P)
        (polynomialLift_reduction p k B σ r hbase P) n hn }
  coordinate_comm i :=
    (Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.frameMap_coefficient p k B A r hr hbase P.base.residueRing P.base.thickening
      (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P.base) (polynomialLift p k B σ r P)
      (polynomialLift_reduction p k B σ r hbase P) n hn (MvPolynomial.X i)).trans (MvPolynomial.aeval_X _ _)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Levels.FramedPolynomialLevels
