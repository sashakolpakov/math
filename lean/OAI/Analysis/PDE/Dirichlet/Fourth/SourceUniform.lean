import OAI.Analysis.PDE.Dirichlet.Fourth.SourceActual
import OAI.Analysis.PDE.Dirichlet.Fourth.CoefficientActual

/-! Uniform control of the genuine second tangent source by lower jets only. -/
noncomputable section
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.Normed.Function.Holder OAI.Analysis.Normed.Function.Holder.HolderMap

variable {n : ℕ} {X : Type} [MetricSpace X] {α : ℝ}
local notation "E" => CoordinateSpace n 4
attribute [local instance] sourceBoundMatrixValueGroup sourceBoundMatrixValueSpace
  sourceBoundScalar1Group sourceBoundScalar1Space sourceBoundScalar2Group sourceBoundScalar2Space
  sourceBoundScalar3Group sourceBoundScalar3Space sourceBoundVector1Group sourceBoundVector1Space
  sourceBoundVector2Group sourceBoundVector2Space sourceBoundVector3Group sourceBoundVector3Space
  sourceBoundMatrixGroup sourceBoundMatrixSpace sourceBoundFirstGroup sourceBoundFirstSpace
  sourceBoundRestGroup sourceBoundRestSpace sourceBoundFullGroup sourceBoundFullSpace

private abbrev suG1 : NormedAddCommGroup (E →L[ℝ] ℝ) := sourceBoundScalar1Group
private abbrev suS1 : NormedSpace ℝ (E →L[ℝ] ℝ) := sourceBoundScalar1Space
attribute [local instance] suG1 suS1
private abbrev suG2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := sourceBoundScalar2Group
private abbrev suS2 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := sourceBoundScalar2Space
attribute [local instance] suG2 suS2
private abbrev suG3 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := sourceBoundScalar3Group
private abbrev suS3 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := sourceBoundScalar3Space
attribute [local instance] suG3 suS3
private abbrev suV1 : NormedAddCommGroup (E →L[ℝ] E) := sourceBoundVector1Group
private abbrev suW1 : NormedSpace ℝ (E →L[ℝ] E) := sourceBoundVector1Space
attribute [local instance] suV1 suW1
private abbrev suV2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := sourceBoundVector2Group
private abbrev suW2 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := sourceBoundVector2Space
attribute [local instance] suV2 suW2
private abbrev suV3 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := sourceBoundVector3Group
private abbrev suW3 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := sourceBoundVector3Space
attribute [local instance] suV3 suW3

structure SecondSourceData (n : ℕ) (X : Type) [MetricSpace X] (α : ℝ) where
  U1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (CoordinateSpace n 4 →L[ℝ] ℝ) α
  U2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) α
  U3 : OAI.Analysis.Normed.Function.Holder.HolderMap X (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) α
  T0 : OAI.Analysis.Normed.Function.Holder.HolderMap X (CoordinateSpace n 4) α
  T1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) α
  T2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) α
  T3 : OAI.Analysis.Normed.Function.Holder.HolderMap X (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) α
  S0 : OAI.Analysis.Normed.Function.Holder.HolderMap X (CoordinateSpace n 4) α
  S1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) α
  S2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) α
  F1 : OAI.Analysis.Normed.Function.Holder.HolderMap X (CoordinateSpace n 4 →L[ℝ] ℝ) α
  F2 : OAI.Analysis.Normed.Function.Holder.HolderMap X (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) α

def SecondSourceData.Bounded (a : SecondSourceData n X α) (R : ℝ) : Prop :=
  ‖a.U1‖ ≤ R ∧ ‖a.U2‖ ≤ R ∧ ‖a.U3‖ ≤ R ∧
  ‖a.T0‖ ≤ R ∧ ‖a.T1‖ ≤ R ∧ ‖a.T2‖ ≤ R ∧ ‖a.T3‖ ≤ R ∧
  ‖a.S0‖ ≤ R ∧ ‖a.S1‖ ≤ R ∧ ‖a.S2‖ ≤ R ∧ ‖a.F1‖ ≤ R ∧ ‖a.F2‖ ≤ R

def SecondSourceData.Realizes (a : SecondSourceData n X α)
    (u f : E → ℝ) (T S : E → E) (ι : X → E) : Prop :=
  (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value a.U1 x = fderiv ℝ u (ι x)) ∧
  (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value a.U2 x = fderiv ℝ (fderiv ℝ u) (ι x)) ∧
  (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value a.U3 x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) (ι x)) ∧
  (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value a.T0 x = T (ι x)) ∧ (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value a.T1 x = fderiv ℝ T (ι x)) ∧
  (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value a.T2 x = fderiv ℝ (fderiv ℝ T) (ι x)) ∧
  (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value a.T3 x = fderiv ℝ (fderiv ℝ (fderiv ℝ T)) (ι x)) ∧
  (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value a.S0 x = S (ι x)) ∧ (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value a.S1 x = fderiv ℝ S (ι x)) ∧
  (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value a.S2 x = fderiv ℝ (fderiv ℝ S) (ι x)) ∧
  (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value a.F1 x = fderiv ℝ f (ι x)) ∧
  (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value a.F2 x = fderiv ℝ (fderiv ℝ f) (ι x))

theorem SecondSourceData.Bounded.mono {a : SecondSourceData n X α} {R Q : ℝ}
    (h : a.Bounded R) (hRQ : R ≤ Q) : a.Bounded Q := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩
  exact ⟨h1.trans hRQ,h2.trans hRQ,h3.trans hRQ,h4.trans hRQ,h5.trans hRQ,h6.trans hRQ,
    h7.trans hRQ,h8.trans hRQ,h9.trans hRQ,h10.trans hRQ,h11.trans hRQ,h12.trans hRQ⟩

def SecondSourceData.jet (a : SecondSourceData n X α) (hα : 0 ≤ α)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α)
    (DA : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α) :
    OAI.Analysis.Normed.Function.Holder.HolderMap X (SecondFieldSourceJet (Fin n × Fin 4)) α :=
  secondFieldJetHolder hα A DA a.U1 a.U2 a.U3 a.T0 a.T1 a.T2 a.T3 a.S0 a.S1 a.S2 a.F1 a.F2

theorem SecondSourceData.norm_jet_le (a : SecondSourceData n X α) (hα : 0 ≤ α)
    {Q : ℝ} (hQ : 1 ≤ Q) (ha : a.Bounded Q)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α)
    (DA : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α)
    (hA : ‖A‖ ≤ Q) (hDA : ‖DA‖ ≤ Q) : ‖a.jet hα A DA‖ ≤ 2*Q^2 := by
  rcases ha with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩
  exact norm_secondFieldJetHolder_le hα hQ A DA a.U1 a.U2 a.U3 a.T0 a.T1 a.T2 a.T3
    a.S0 a.S1 a.S2 a.F1 a.F2 hA hDA h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem SecondSourceData.jet_actual (a : SecondSourceData n X α) (hα : 0 ≤ α)
    (u f : E → ℝ) (T S : E → E) (ι : X → E) (ha : a.Realizes u f T S ι)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α)
    (DA : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α)
    (eA : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (ι x)))
    (eDA : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value DA x = fderiv ℝ
      (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) (ι x)) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F := SecondFieldSourceJet (Fin n × Fin 4)) (a.jet hα A DA) x = secondFieldSourceJet
      (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) u f T S (ι x) := by
  rcases ha with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩
  exact secondFieldJetHolder_actual hα A DA a.U1 a.U2 a.U3 a.T0 a.T1 a.T2 a.T3
    a.S0 a.S1 a.S2 a.F1 a.F2 _ u f T S x (ι x)
    (eA x) (eDA x) (h1 x) (h2 x) (h3 x) (h4 x) (h5 x) (h6 x) (h7 x)
    (h8 x) (h9 x) (h10 x) (h11 x) (h12 x)

/-- The constant is chosen before the potential, forcing and tangent fields.
The potential is controlled only through its first three actual derivatives. -/
theorem exists_uniform_moore_second_source_bound (hα : 0 ≤ α) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u f : E → ℝ) (T S : E → E),
      ContDiff ℝ 3 u → ContDiff ℝ 2 f → ContDiff ℝ 3 T → ∀ (ι : X → E)
      (a : SecondSourceData n X α), a.Bounded R → a.Realizes u f T S ι →
      ∃ F : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = mooreSecondFieldForcing u f T S (ι x)) ∧ ‖F‖ ≤ C := by
  obtain ⟨B,hB,hcoef⟩ := exists_actual_mooreCoefficient_jet_holder_bound (n := n) (X := X) hα hR
  let Q := 1 + R + B
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith
  have hRQ : R ≤ Q := by dsimp [Q]; linarith
  have hBQ : B ≤ Q := by dsimp [Q]; linarith
  obtain ⟨C,hC,hsource⟩ := exists_moore_second_source_bound_of_jet (n := n) (X := X)
    hα (show 0 ≤ 2 * Q^2 by positivity)
  refine ⟨C,hC,?_⟩
  intro u f T S hu hf hT ι a ha ea
  obtain ⟨A,DA,eA,eDA,hA,hDA⟩ :=
    hcoef u hu ι a.U2 a.U3 ha.2.1 ha.2.2.1 ea.2.1 ea.2.2.1
  exact hsource u f T S hu hf hT ι (a.jet hα A DA)
    (a.norm_jet_le hα hQ (ha.mono hRQ) A DA (hA.trans hBQ) (hDA.trans hBQ))
    (a.jet_actual hα u f T S ι ea A DA eA eDA)

end OAI.Analysis.PDE.Dirichlet
