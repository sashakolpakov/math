import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.LimitEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.TermLimit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators

/-! # Section Differential -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SectionDifferential.CrystallineFrameSectionDifferential

noncomputable section

/-!
# The native frame section equivalence preserves the differential

Actual evaluation intertwines the coefficient derivatives. Tensoring
with exterior coordinates then gives the equality of differentials in
every degree of the native section complex.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "Native" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution.complex p k B σ a
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase
local notation "Completed" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B Tower
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators.AffinePolynomialOperators.derivative p k B σ r hr hbase
local notation "πF" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.FunctionLimit.CrystallineFrameFunctionLimit.completedCone p k B σ r hr hbase

theorem coefficient_derivative (Q : Native) (i : σ) (x : Completed) :
    (πF).π.app (op Q) (D i x) =
      PDDerivatives.CrystallineFramePDDerivatives.derivation p k B σ a Q i ((πF).π.app (op Q) x) := by
  classical
  obtain ⟨n, hn⟩ := ((G).obj Q).base.thickening.p_nilpotent
  have hn' : (p : ((G).obj Q).base.thickening.ring) ^ (n + 1) = 0 := by
    rw [pow_succ, hn, zero_mul]
  rw [LimitEvaluation.CrystallineFrameLimitEvaluation.native_eval p k B σ r hr hbase Q n hn',
    LimitEvaluation.CrystallineFrameLimitEvaluation.native_eval p k B σ r hr hbase Q n hn',
    Affine.PolynomialOperators.AffinePolynomialOperators.eval_derivative]
  exact (EvaluationDerivative.CrystallineFrameEvaluationDerivative.naturality p k B σ r hr hbase Q n hn' i
    (PD.InverseLimit.PDInverseLimit.eval p k B Tower n x)).symm

variable [Fintype σ] [LinearOrder σ]

def differentialMap (n : ℕ) :
    (TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase n).pt ⟶
      (TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase (n + 1)).pt :=
  ModuleCat.ofHom (Koszul.Tensor.KoszulTensor.differential W σ Completed D n)

omit [LinearOrder σ] in
theorem raw_d (n : ℕ) (Q : Nativeᵒᵖ) : ((K).d n (n + 1)).app Q =
    ModuleCat.ofHom (Koszul.Tensor.KoszulTensor.differential W σ ((F).obj Q)
      (Koszul.Functor.KoszulFunctor.derivatives W σ F (Operators.CrystallineFrameOperators.derivative p k B σ a) Q) n) := by
  change (Koszul.Tensor.KoszulTensor.complex W σ ((F).obj Q)
    (Koszul.Functor.KoszulFunctor.derivatives W σ F (Operators.CrystallineFrameOperators.derivative p k B σ a) Q)
    (Resolution.CrystallineFrameResolution.commute p k B σ a Q)).d n (n + 1) = _
  exact CochainComplex.of_d (fun j => ModuleCat.of W (Koszul.Tensor.KoszulTensor.Term W σ ((F).obj Q) j))
    (fun j => ModuleCat.ofHom (Koszul.Tensor.KoszulTensor.differential W σ ((F).obj Q)
      (Koszul.Functor.KoszulFunctor.derivatives W σ F (Operators.CrystallineFrameOperators.derivative p k B σ a) Q) j)) n

omit [LinearOrder σ] in
theorem differential (n : ℕ) (Q : Nativeᵒᵖ) :
    differentialMap p k B σ r hr hbase n ≫
      (TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase (n + 1)).π.app Q =
        (TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase n).π.app Q ≫ ((K).d n (n + 1)).app Q := by
  rw [raw_d]
  apply ModuleCat.hom_ext
  change (TensorProduct.map ((πF).π.app Q).hom LinearMap.id).comp
    (Koszul.Tensor.KoszulTensor.differential W σ Completed D n) =
      (Koszul.Tensor.KoszulTensor.differential W σ ((F).obj Q)
        (Koszul.Functor.KoszulFunctor.derivatives W σ F (Operators.CrystallineFrameOperators.derivative p k B σ a) Q) n).comp
          (TensorProduct.map ((πF).π.app Q).hom LinearMap.id)
  exact Koszul.TensorMap.KoszulTensorMap.differential_naturality W σ Completed ((F).obj Q) D
    (Koszul.Functor.KoszulFunctor.derivatives W σ F (Operators.CrystallineFrameOperators.derivative p k B σ a) Q)
    ((πF).π.app Q).hom (fun i x => coefficient_derivative p k B σ r hr hbase Q.unop i x) n

theorem sectionsEquiv_differential (n : ℕ)
    (s : (Functor.const Nativeᵒᵖ).obj (ModuleCat.of W W) ⟶ (K).X n) :
    TermLimit.CrystallineFrameTermLimit.sectionsEquiv p k B σ r hr hbase (n + 1) (s ≫ (K).d n (n + 1)) =
      Koszul.Tensor.KoszulTensor.differential W σ Completed D n
        (TermLimit.CrystallineFrameTermLimit.sectionsEquiv p k B σ r hr hbase n s) :=
  Module.ConeSections.ModuleConeSections.naturality W
    (TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase n)
    (TermLimit.CrystallineFrameTermLimit.isLimit p k B σ r hr hbase n)
    (TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase (n + 1))
    (TermLimit.CrystallineFrameTermLimit.isLimit p k B σ r hr hbase (n + 1))
    ((K).d n (n + 1)) (differentialMap p k B σ r hr hbase n)
    (differential p k B σ r hr hbase n) s

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SectionDifferential.CrystallineFrameSectionDifferential
