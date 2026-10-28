import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedSectionEvaluation

/-! # Section Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.SectionEvaluation.AffineSectionEvaluation

noncomputable section

/-! # The original completed comparison evaluated on actual native sheaf sections -/

open _root_.CategoryTheory Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff) [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "Poly" => MvPolynomial σ W
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "Native" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "KS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution.complex p k B σ a
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B Poly r hr hbase
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase

def evaluation (j n : ℕ) :
    ((K).X j).obj (op (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n)) →ₗ[W]
      PD.DeRham.PDDeRham.Form W (T n).ring (RingHom.ker (T n).reduction) (T n).dividedPowers j :=
  ((PD.FormsTensor.PDFormsTensor.toForms W (T n).ring σ (RingHom.ker (T n).reduction) (T n).dividedPowers
      (fun i => EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B Poly r hr hbase n (MvPolynomial.X i)) j).restrictScalars W).comp
        (CrystallineFrame.TermEvaluation.CrystallineFrameTermEvaluation.evaluation p k B σ r hr hbase n j)

theorem component_down (j : ℕ)
    (s : (Functor.const Nativeᵒᵖ).obj (ModuleCat.of R R) ⟶ ((KS).X j).obj) :
    ((Comparison.AffineCrystallineComparison.complexIso p k B σ r hr hbase).hom.f j (ULift.up s)).down.down =
      (PolynomialComparison.AffinePolynomialComparison.complexIso p k B σ r hr hbase).hom.f j
        (LiftedTermLimit.CrystallineLiftedTermLimit.sectionsEquiv p k B σ r hr hbase j s).down := rfl

theorem component (j n : ℕ)
    (s : (Functor.const Nativeᵒᵖ).obj (ModuleCat.of R R) ⟶ ((KS).X j).obj) :
    PD.PDDeRham.eval p k B Tower j n
      (((Comparison.AffineCrystallineComparison.complexIso p k B σ r hr hbase).hom.f j (ULift.up s)).down.down) =
    evaluation p k B σ r hr hbase j n
      (((CrystallineFrame.SheafCech.CrystallineFrameSheafCech.sectionPresheafIso p k B σ a j).hom.app
        (op (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n))
          (s.app (op (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n)) (1 : R))).down) := by
  have hc := PolynomialEvaluation.AffinePolynomialEvaluation.component p k B σ r hr hbase j n
    (LiftedTermLimit.CrystallineLiftedTermLimit.sectionsEquiv p k B σ r hr hbase j s).down
  have hs := LiftedSectionEvaluation.CrystallineLiftedSectionEvaluation.evaluation p k B σ r hr hbase j n s
  exact (congrArg (PD.PDDeRham.eval p k B Tower j n)
    (component_down p k B σ r hr hbase j s)).trans
      (hc.trans (congrArg
        (PD.FormsTensor.PDFormsTensor.toForms W (T n).ring σ (RingHom.ker (T n).reduction) (T n).dividedPowers
          (fun i => EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B Poly r hr hbase n (MvPolynomial.X i)) j)
        hs.symm))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.SectionEvaluation.AffineSectionEvaluation
