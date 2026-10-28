import OAI.Analysis.PDE.Dirichlet.Fourth.SourceJet

/-! An explicit lower-jet expression for the twice differentiated source. -/
noncomputable section
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.PDE.Elliptic OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

local instance secondSourceCLMGroup (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance secondSourceCLMSpace (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (E →L[ℝ] F) := inferInstance

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I
local instance sourceExprMatrixValueGroup : NormedAddCommGroup (Matrix I I ℝ) :=
  inferInstanceAs (NormedAddCommGroup (I → I → ℝ))
local instance sourceExprMatrixValueSpace : NormedSpace ℝ (Matrix I I ℝ) :=
  inferInstanceAs (NormedSpace ℝ (I → I → ℝ))
local instance sourceExprScalar1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance sourceExprScalar1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance sourceExprScalar2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceExprScalar2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceExprScalar3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceExprScalar3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceExprVector1Group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance sourceExprVector1Space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance sourceExprVector2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceExprVector2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceExprVector3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceExprVector3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceExprMatrixGroup : NormedAddCommGroup (E →L[ℝ] Matrix I I ℝ) :=
  inferInstanceAs (NormedAddCommGroup (E →L[ℝ] (I → I → ℝ)))
local instance sourceExprMatrixSpace : NormedSpace ℝ (E →L[ℝ] Matrix I I ℝ) :=
  inferInstanceAs (NormedSpace ℝ (E →L[ℝ] (I → I → ℝ)))
local instance sourceExprFirstGroup : NormedAddCommGroup (FirstFieldJet I) := by
  unfold FirstFieldJet
  infer_instance
local instance sourceExprFirstSpace : NormedSpace ℝ (FirstFieldJet I) := by
  unfold FirstFieldJet
  infer_instance
local instance sourceExprFirstDualGroup : NormedAddCommGroup (FirstFieldJet I →L[ℝ] ℝ) := by
  exact ContinuousLinearMap.toNormedAddCommGroup
local instance sourceExprFirstDualSpace : NormedSpace ℝ (FirstFieldJet I →L[ℝ] ℝ) := by
  exact ContinuousLinearMap.toNormedSpace

def fieldFirstExpression (z : FirstFieldJet I) (v : E) : ℝ :=
  z.1.1.2 (z.2.1.1 v) + z.1.2.1 v z.1.2.2

def fieldSecondExpression (z : FirstFieldJet I) (U : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (v w : E) : ℝ :=
  U v w z.1.2.2 + z.1.2.1 v (z.2.1.1 w) + z.1.2.1 w (z.2.1.1 v) +
    z.1.1.2 (z.2.1.2 v w)

omit [DecidableEq I] in
@[fun_prop] theorem contDiff_fieldFirstExpression {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {k : WithTop ℕ∞}
    {z : V → FirstFieldJet I} {v : V → E} (hz : ContDiff ℝ k z) (hv : ContDiff ℝ k v) :
    ContDiff ℝ k (fun x => fieldFirstExpression (z x) (v x)) := by
  unfold fieldFirstExpression
  fun_prop

omit [DecidableEq I] in
@[fun_prop] theorem contDiff_fieldSecondExpression {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {k : WithTop ℕ∞}
    {z : V → FirstFieldJet I} {U : V → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    {v w : V → E} (hz : ContDiff ℝ k z) (hU : ContDiff ℝ k U)
    (hv : ContDiff ℝ k v) (hw : ContDiff ℝ k w) :
    ContDiff ℝ k (fun x => fieldSecondExpression (z x) (U x) (v x) (w x)) := by
  unfold fieldSecondExpression
  fun_prop

abbrev SecondFieldRestJet (I : Type*) [Fintype I] :=
  ((EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) ×
    (EuclideanSpace ℝ I →L[ℝ] Matrix I I ℝ)) ×
    (EuclideanSpace ℝ I × ((EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) ×
      (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)))

local instance sourceExprRestGroup : NormedAddCommGroup (SecondFieldRestJet I) := by
  unfold SecondFieldRestJet
  infer_instance
local instance sourceExprRestSpace : NormedSpace ℝ (SecondFieldRestJet I) := by
  unfold SecondFieldRestJet
  infer_instance

def fieldCommutatorExpression (z : FirstFieldJet I) (q : SecondFieldRestJet I) : ℝ :=
  (∑ i : I, ∑ j : I, z.1.1.1 i j *
    (fieldSecondExpression z q.1.1 (EuclideanSpace.single i 1)
        (q.2.2.1 (EuclideanSpace.single j 1)) +
      fieldSecondExpression z q.1.1 (EuclideanSpace.single j 1)
        (q.2.2.1 (EuclideanSpace.single i 1)) +
      fieldFirstExpression z (q.2.2.2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)))) -
    ∑ i : I, ∑ j : I, (q.1.2 q.2.1) i j *
      fieldSecondExpression z q.1.1 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

@[fun_prop] theorem contDiff_fieldCommutatorExpression {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {k : WithTop ℕ∞}
    {z : V → FirstFieldJet I} {q : V → SecondFieldRestJet I}
    (hz : ContDiff ℝ k z) (hq : ContDiff ℝ k q) :
    ContDiff ℝ k (fun x => fieldCommutatorExpression (z x) (q x)) := by
  unfold fieldCommutatorExpression
  fun_prop

abbrev SecondFieldSourceJet (I : Type*) [Fintype I] :=
  (FirstFieldJet I × FirstFieldJet I) × SecondFieldRestJet I

local instance sourceExprFullGroup : NormedAddCommGroup (SecondFieldSourceJet I) := inferInstance
local instance sourceExprFullSpace : NormedSpace ℝ (SecondFieldSourceJet I) := inferInstance

def secondFieldExpression (z : SecondFieldSourceJet I) : ℝ :=
  fderiv ℝ firstFieldExpression z.1.1 z.1.2 + fieldCommutatorExpression z.1.1 z.2

theorem contDiff_secondFieldExpression (k : WithTop ℕ∞) :
    ContDiff ℝ k (secondFieldExpression (I := I)) := by
  have hD : ContDiff ℝ k (fderiv ℝ (firstFieldExpression (I := I))) :=
    (contDiff_firstFieldExpression (I := I) (k + 1)).fderiv_right (m := k) le_rfl
  unfold secondFieldExpression
  apply ContDiff.add
  · exact (hD.comp (contDiff_fst.comp contDiff_fst)).clm_apply
      (contDiff_snd.comp contDiff_fst)
  · exact contDiff_fieldCommutatorExpression (contDiff_fst.comp contDiff_fst) contDiff_snd

def secondFieldRestJet (A : E → Matrix I I ℝ) (u : E → ℝ) (S : E → E)
    (x : E) : SecondFieldRestJet I :=
  ((fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x, fderiv ℝ A x),
    (S x, (fderiv ℝ S x, fderiv ℝ (fderiv ℝ S) x)))

theorem fieldCommutatorExpression_jet (A : E → Matrix I I ℝ) (u f : E → ℝ)
    (T S : E → E) (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 3 u)
    (hT : ContDiff ℝ 2 T) (x : E) :
    fieldCommutatorExpression (firstFieldJet A u f T x) (secondFieldRestJet A u S x) =
      indexedFieldCommutator A (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) S x := by
  have hAe (i j : I) :
      fderiv ℝ (fun y => A y i j) x (S x) = (fderiv ℝ A x (S x)) i j := by
    rw [fderiv_apply ((contDiff_pi.mp hA i).differentiable one_ne_zero x) j,
      fderiv_apply (hA.differentiable one_ne_zero x) i]
    rfl
  unfold fieldCommutatorExpression indexedFieldCommutator indexedFieldCorrection
    indexedNondivergenceOperator
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [OAI.Analysis.PDE.Elliptic.hessian_fieldDerivative hu hT, OAI.Analysis.PDE.Elliptic.hessian_fieldDerivative hu hT]
    have h1 := OAI.Analysis.PDE.Elliptic.directionalDerivative_fieldDerivative (hu.of_le (by norm_num))
      (hT.differentiable (by norm_num))
      (fderiv ℝ (fderiv ℝ S) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) x
    exact congrArg (fun z => A x i j *
      (fieldSecondExpression (firstFieldJet A u f T x)
        (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) (EuclideanSpace.single i 1)
        (fderiv ℝ S x (EuclideanSpace.single j 1)) +
      fieldSecondExpression (firstFieldJet A u f T x)
        (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) (EuclideanSpace.single j 1)
        (fderiv ℝ S x (EuclideanSpace.single i 1)) + z)) h1.symm
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [OAI.Analysis.PDE.Elliptic.hessian_fieldDerivative hu hT]
    change (fderiv ℝ A x (S x)) i j * _ = fderiv ℝ (fun y => A y i j) x (S x) * _
    rw [hAe]
    rfl

def secondFieldSourceJet (A : E → Matrix I I ℝ) (u f : E → ℝ)
    (T S : E → E) (x : E) : SecondFieldSourceJet I :=
  ((firstFieldJet A u f T x, firstFieldJetDifferential A u f T x (S x)),
    secondFieldRestJet A u S x)

theorem secondFieldExpression_jet (A : E → Matrix I I ℝ) (u f : E → ℝ)
    (T S : E → E) (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 3 u)
    (hf : ContDiff ℝ 2 f) (hT : ContDiff ℝ 3 T) (x : E) :
    secondFieldExpression (secondFieldSourceJet A u f T S x) =
      OAI.Analysis.PDE.Elliptic.fieldDerivative (fun y => OAI.Analysis.PDE.Elliptic.fieldDerivative f T y + indexedFieldCorrection A u T y) S x +
        indexedFieldCommutator A (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) S x := by
  change fderiv ℝ firstFieldExpression (firstFieldJet A u f T x)
    (firstFieldJetDifferential A u f T x (S x)) +
    fieldCommutatorExpression (firstFieldJet A u f T x) (secondFieldRestJet A u S x) = _
  rw [← first_field_source_derivative A u f T S hA hu hf hT,
    fieldCommutatorExpression_jet A u f T S hA hu (hT.of_le (by norm_num))]

theorem mooreSecondFieldForcing_eq_expression {n : ℕ}
    (u f : CoordinateSpace n 4 → ℝ) (T S : CoordinateSpace n 4 → CoordinateSpace n 4)
    (hu : ContDiff ℝ 3 u) (hf : ContDiff ℝ 2 f) (hT : ContDiff ℝ 3 T)
    (x : CoordinateSpace n 4) :
    mooreSecondFieldForcing u f T S x = secondFieldExpression
      (secondFieldSourceJet (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
        u f T S x) := by
  exact (secondFieldExpression_jet _ u f T S
    ((contDiff_mooreRealMatrix n 1).comp (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots hu))
    hu hf hT x).symm

end OAI.Analysis.PDE.Dirichlet
