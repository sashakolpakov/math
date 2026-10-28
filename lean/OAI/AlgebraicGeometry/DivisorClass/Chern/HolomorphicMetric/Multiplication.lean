import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.ScalarAction
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral

/-! # Multiplication -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! Smooth metric-ratio multiplication implements the exact change in the original metric integral. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h k : Data.HolomorphicLineMetricData u)

def Data.HolomorphicLineMetricData.ratioOpenFunction :
    SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) (⊤ : Opens V.analyticSpace) :=
  ⟨fun x => (h.ratio k x.val : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp
    ((h.ratio_smooth k).comp (contMDiff_subtype_val (I := 𝓘(ℝ, V.analyticModel))))⟩

def Data.HolomorphicLineMetricData.ratioFormMul (n : ℕ) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n :=
  HolomorphicSmooth.ScalarAction.holomorphicLineSmoothScalarMul u n (h.ratioOpenFunction V k)

theorem Data.HolomorphicLineMetricData.ratioFormMul_apply (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (i : V.analyticSpace) (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    (h.ratioFormMul V k n a).val i x = (h.ratio k x.val : ℂ) • a.val i x :=
  HolomorphicSmooth.ScalarAction.holomorphicLineSmoothScalarMul_apply u n (h.ratioOpenFunction V k) a i x

theorem Data.HolomorphicLineMetricData.ratioFormMul_comp (l : Data.HolomorphicLineMetricData u)
    (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    h.ratioFormMul V k n (k.ratioFormMul V l n a) = h.ratioFormMul V l n a := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro i x
  rw [h.ratioFormMul_apply, k.ratioFormMul_apply, h.ratioFormMul_apply,
    smul_smul, ← Complex.ofReal_mul, h.ratio_mul k l x.val]

theorem Data.HolomorphicLineMetricData.ratioFormMul_self (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    h.ratioFormMul V h n a = a := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro i x
  rw [h.ratioFormMul_apply, h.ratio_self, Complex.ofReal_one, one_smul]

theorem Data.HolomorphicLineMetricData.ratioFormMul_cancel (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    h.ratioFormMul V k n (k.ratioFormMul V h n a) = a := by
  rw [h.ratioFormMul_comp, h.ratioFormMul_self]

theorem Data.HolomorphicLineMetricData.globalFormPair_scalar_left (n : ℕ)
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) (⊤ : Opens V.analyticSpace))
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (x : V.analyticSpace) :
    h.globalFormPair V n (HolomorphicSmooth.ScalarAction.holomorphicLineSmoothScalarMul u n f a) b x =
      conj (f ⟨x, trivial⟩) * h.globalFormPair V n a b x := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x
  rw [h.globalFormPair_inFrame V n _ b x x hx, h.globalFormPair_inFrame V n a b x x hx,
    HolomorphicSmooth.ScalarAction.holomorphicLineSmoothScalarMul_apply, Projective.CovectorPair.projectiveTangentCovectorPair_smul_left]
  ring

theorem Data.HolomorphicLineMetricData.globalFormPair_ratio_left (n : ℕ)
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (x : V.analyticSpace) :
    k.globalFormPair V n (h.ratioFormMul V k n a) b x = h.globalFormPair V n a b x := by
  rw [Data.HolomorphicLineMetricData.ratioFormMul, k.globalFormPair_scalar_left]
  change conj (h.ratio k x : ℂ) * k.globalFormPair V n a b x = h.globalFormPair V n a b x
  rw [Complex.conj_ofReal]
  exact (h.globalFormPair_change V n k a b x).symm

theorem Data.HolomorphicLineMetricData.formIntegralPair_change_left (n : ℕ)
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    h.formIntegralPair V n a b = k.formIntegralPair V n (h.ratioFormMul V k n a) b := by
  unfold Data.HolomorphicLineMetricData.formIntegralPair
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => (h.globalFormPair_ratio_left V k n a b x).symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
