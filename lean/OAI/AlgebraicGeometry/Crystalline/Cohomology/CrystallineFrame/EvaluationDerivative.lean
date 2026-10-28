import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivativeMaps
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PDDerivatives

/-! # Evaluation Derivative -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.EvaluationDerivative.CrystallineFrameEvaluationDerivative

noncomputable section

/-!
# The native differential commutes with evaluating the original envelope

The actual map from a p-power envelope level to a native free frame
preserves total coordinates. Its PD evaluation therefore intertwines
the envelope coordinate derivative and the native frame differential.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "P" => Functor.obj (OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a) Q
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B Poly r hr hbase
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PDDerivatives.CrystallineFramePDDerivatives.derivation p k B σ a Q

def evaluate (n : ℕ) (hn : (p : (P).base.thickening.ring) ^ (n + 1) = 0) :
    (T n).ring →ₐ[W] (P).base.thickening.ring :=
  (FramedPolynomial.Levels.FramedPolynomialLevels.map p k B σ r hr hbase P n hn).hom.ambientMap

theorem naturality [DecidableEq σ] (n : ℕ)
    (hn : (p : (P).base.thickening.ring) ^ (n + 1) = 0) (i : σ) (x : (T n).ring) :
    D i (evaluate p k B σ r hr hbase Q n hn x) =
      evaluate p k B σ r hr hbase Q n hn
        (Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation p k B σ r hr hbase n i x) := by
  apply Affine.PolynomialFrameDerivativeMaps.AffinePolynomialFrameDerivativeMaps.naturality p k B σ r hr hbase
    (P).base.residueRing (P).base.thickening
    (AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B (P).base)
    (FramedPolynomial.Levels.FramedPolynomialLevels.polynomialLift p k B σ r P)
    (FramedPolynomial.Levels.FramedPolynomialLevels.polynomialLift_reduction p k B σ r hbase P) (D i)
    (PDDerivatives.CrystallineFramePDDerivatives.dpow p k B σ a Q i) i
    (n := n) (hn := hn)
  intro j
  change D i (MvPolynomial.aeval (P).coordinate (MvPolynomial.X j)) = _
  rw [MvPolynomial.aeval_X]
  exact PDDerivatives.CrystallineFramePDDerivatives.coordinate p k B σ a Q i j

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.EvaluationDerivative.CrystallineFrameEvaluationDerivative
