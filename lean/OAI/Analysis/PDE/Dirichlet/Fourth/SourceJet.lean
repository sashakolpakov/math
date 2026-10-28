import OAI.Analysis.PDE.Dirichlet.Fourth.FieldEquation
import OAI.Analysis.Normed.Function.Holder.DirichletFourthSourceHolder

/-! The first differentiated equation is a smooth function of an explicit
finite jet. Its derivative uses only the third jet of the unknown. -/
noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.PDE.Elliptic OAI.Analysis.Normed.Function.Holder

private theorem hasFDerivAt_seven
    {V A B C D F G H : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a : V → A} {b : V → B} {c : V → C} {d : V → D}
    {f : V → F} {g : V → G} {h : V → H}
    {a' : V →L[ℝ] A} {b' : V →L[ℝ] B} {c' : V →L[ℝ] C} {d' : V →L[ℝ] D}
    {f' : V →L[ℝ] F} {g' : V →L[ℝ] G} {h' : V →L[ℝ] H} {x : V}
    (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) (hc : HasFDerivAt c c' x)
    (hd : HasFDerivAt d d' x) (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hh : HasFDerivAt h h' x) :
    HasFDerivAt (fun y => (((a y, b y), (c y, d y)), ((f y, g y), h y)))
      (((a'.prod b').prod (c'.prod d')).prod ((f'.prod g').prod h')) x :=
  ((ha.prodMk hb).prodMk (hc.prodMk hd)).prodMk ((hf.prodMk hg).prodMk hh)

local instance sourceJetCLMGroup (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance sourceJetCLMSpace (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance sourceJetCLMAdd (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    AddCommGroup (E →L[ℝ] F) := inferInstance
local instance sourceJetCLMModule (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Module ℝ (E →L[ℝ] F) := inferInstance

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I
local instance sourceJetEuclideanAdd : AddCommGroup E := inferInstance
local instance sourceJetEuclideanModule : Module ℝ E := inferInstance
local instance sourceJetScalar1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance sourceJetScalar1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance sourceJetScalar2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceJetScalar2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceJetScalar3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceJetScalar3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceJetVector1Group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance sourceJetVector1Space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance sourceJetVector2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceJetVector2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceJetVector3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceJetVector3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceJetScalarFirstAdd : AddCommMonoid (E →L[ℝ] ℝ) := inferInstance
local instance sourceJetScalarSecondAdd : AddCommMonoid (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance sourceJetVectorFirstAdd : AddCommMonoid (E →L[ℝ] E) := inferInstance
local instance sourceJetVectorSecondAdd : AddCommMonoid (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceJetLeftAdd :
    AddCommMonoid ((Matrix I I ℝ × (E →L[ℝ] ℝ)) × (E →L[ℝ] E →L[ℝ] ℝ) × E) := inferInstance
local instance sourceJetRightAdd :
    AddCommMonoid (((E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E)) × (E →L[ℝ] ℝ)) := inferInstance
local instance sourceJetLeftGroup :
    NormedAddCommGroup ((Matrix I I ℝ × (E →L[ℝ] ℝ)) × (E →L[ℝ] E →L[ℝ] ℝ) × E) := inferInstance
local instance sourceJetLeftSpace :
    NormedSpace ℝ ((Matrix I I ℝ × (E →L[ℝ] ℝ)) × (E →L[ℝ] E →L[ℝ] ℝ) × E) := inferInstance
local instance sourceJetRightGroup :
    NormedAddCommGroup (((E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E)) × (E →L[ℝ] ℝ)) := inferInstance
local instance sourceJetRightSpace :
    NormedSpace ℝ (((E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E)) × (E →L[ℝ] ℝ)) := inferInstance

abbrev FirstFieldJet (I : Type*) [Fintype I] :=
  ((Matrix I I ℝ × (EuclideanSpace ℝ I →L[ℝ] ℝ)) ×
    ((EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) × EuclideanSpace ℝ I)) ×
    (((EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) ×
      (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)) ×
      (EuclideanSpace ℝ I →L[ℝ] ℝ))

local instance sourceJetFullGroup : NormedAddCommGroup (FirstFieldJet I) := inferInstance
local instance sourceJetFullSpace : NormedSpace ℝ (FirstFieldJet I) := inferInstance

def firstFieldExpression (z : FirstFieldJet I) : ℝ :=
  z.2.2 z.1.2.2 + ∑ i : I, ∑ j : I, z.1.1.1 i j *
    (z.1.2.1 (EuclideanSpace.single i 1) (z.2.1.1 (EuclideanSpace.single j 1)) +
      z.1.2.1 (EuclideanSpace.single j 1) (z.2.1.1 (EuclideanSpace.single i 1)) +
      z.1.1.2 (z.2.1.2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)))

theorem contDiff_firstFieldExpression (k : WithTop ℕ∞) :
    ContDiff ℝ k (firstFieldExpression (I := I)) := by
  unfold firstFieldExpression
  fun_prop

def firstFieldJet (A : E → Matrix I I ℝ) (u f : E → ℝ) (T : E → E) (x : E) :
    FirstFieldJet I :=
  (((A x, fderiv ℝ u x), (fderiv ℝ (fderiv ℝ u) x, T x)),
    ((fderiv ℝ T x, fderiv ℝ (fderiv ℝ T) x), fderiv ℝ f x))

@[simp] theorem firstFieldExpression_jet (A : E → Matrix I I ℝ)
    (u f : E → ℝ) (T : E → E) (x : E) :
    firstFieldExpression (firstFieldJet A u f T x) =
      OAI.Analysis.PDE.Elliptic.fieldDerivative f T x + indexedFieldCorrection A u T x := rfl

def firstFieldJetDifferential (A : E → Matrix I I ℝ) (u f : E → ℝ)
    (T : E → E) (x : E) : E →L[ℝ] FirstFieldJet I :=
  (((fderiv ℝ A x).prod (fderiv ℝ (fderiv ℝ u) x)).prod
    ((fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x).prod (fderiv ℝ T x))).prod
      (((fderiv ℝ (fderiv ℝ T) x).prod (fderiv ℝ (fderiv ℝ (fderiv ℝ T)) x)).prod
        (fderiv ℝ (fderiv ℝ f) x))

omit [DecidableEq I] in
theorem hasFDerivAt_firstFieldJet (A : E → Matrix I I ℝ) (u f : E → ℝ)
    (T : E → E) (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 3 u)
    (hf : ContDiff ℝ 2 f) (hT : ContDiff ℝ 3 T) (x : E) :
    HasFDerivAt (firstFieldJet A u f T) (firstFieldJetDifferential A u f T x) x := by
  have hu1 : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hu2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) := hu1.fderiv_right (by norm_num)
  have hT1 : ContDiff ℝ 2 (fderiv ℝ T) := hT.fderiv_right (by norm_num)
  have hT2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ T)) := hT1.fderiv_right (by norm_num)
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact hasFDerivAt_seven (hA.differentiable one_ne_zero x).hasFDerivAt
    (hu1.differentiable (by norm_num) x).hasFDerivAt
    (hu2.differentiable one_ne_zero x).hasFDerivAt
    (hT.differentiable (by norm_num) x).hasFDerivAt
    (hT1.differentiable (by norm_num) x).hasFDerivAt
    (hT2.differentiable one_ne_zero x).hasFDerivAt
    (hf1.differentiable one_ne_zero x).hasFDerivAt

theorem first_field_source_derivative (A : E → Matrix I I ℝ) (u f : E → ℝ)
    (T S : E → E) (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 3 u)
    (hf : ContDiff ℝ 2 f) (hT : ContDiff ℝ 3 T) (x : E) :
    OAI.Analysis.PDE.Elliptic.fieldDerivative (fun y => OAI.Analysis.PDE.Elliptic.fieldDerivative f T y + indexedFieldCorrection A u T y) S x =
      fderiv ℝ firstFieldExpression (firstFieldJet A u f T x)
        (firstFieldJetDifferential A u f T x (S x)) := by
  have h := ((contDiff_firstFieldExpression (I := I) 1).differentiable one_ne_zero
    (firstFieldJet A u f T x)).hasFDerivAt.comp x
      (hasFDerivAt_firstFieldJet A u f T hA hu hf hT x)
  exact congrArg (fun L : E →L[ℝ] ℝ => L (S x)) h.fderiv

end OAI.Analysis.PDE.Dirichlet
