import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices

/-! # Intrinsic Compact Projector -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter

/-! Explicit local projector coordinates for compact-place invariant
Hodge subspaces. The ambient matrix parameters give holomorphic
extensions of the actual compact-choice projectors. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

abbrev ProjectorParameters := Fin A.places →
  Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ

def baseParameter : ProjectorParameters A := fun v =>
  (Matrix.diagonal (fun j => if A.positive v j then 1 else 0),
   Matrix.diagonal (fun j => if A.positive v j then 0 else 1))

def choiceParameter (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) : ProjectorParameters A := fun v =>
  ((p.change v).val * (baseParameter A v).1 * (p.change v).inv,
   (p.change v).invᵀ * (baseParameter A v).2 * (p.change v).valᵀ)

def ambientParameter (p : ProjectorParameters A) (z : IntrinsicExterior.Intrinsic.Tangent) (w : Adelic.BallGeometryData.ComplexPhase A) : Adelic.BallGeometryData.ComplexPhase A :=
  fun v => if v = A.distinguished then
    (fun ij => Adelic.DeterminantCoordinates.lineVector z ij.1 * (w v).1 (2,ij.2),
     fun ij => Adelic.DeterminantCoordinates.annihilatorVector z 0 ij.1 * (w v).2 (0,ij.2) +
       Adelic.DeterminantCoordinates.annihilatorVector z 1 ij.1 * (w v).2 (1,ij.2))
  else
    (fun ij => ∑ r, (p v).1 ij.2 r * (w v).1 (ij.1,r),
     fun ij => ∑ r, (p v).2 ij.2 r * (w v).2 (ij.1,r))

theorem ambientParameter_holomorphic (w : Adelic.BallGeometryData.ComplexPhase A) :
    Differentiable ℂ (fun q : ProjectorParameters A × IntrinsicExterior.Intrinsic.Tangent => ambientParameter A q.1 q.2 w) := by
  apply differentiable_pi.mpr
  intro v
  by_cases hv : v = A.distinguished
  · simp only [ambientParameter,ite_eq_left hv]
    apply Differentiable.prodMk
    · apply differentiable_pi.mpr
      rintro ⟨i,j⟩
      fin_cases i <;> dsimp [Adelic.DeterminantCoordinates.lineVector] <;> fun_prop
    · apply differentiable_pi.mpr
      rintro ⟨i,j⟩
      fin_cases i <;> dsimp [Adelic.DeterminantCoordinates.annihilatorVector] <;> fun_prop
  · simp only [ambientParameter,ite_eq_right hv]
    apply Differentiable.prodMk
    all_goals
      apply differentiable_pi.mpr
      intro ij
      fun_prop

theorem ambientParameter_base (z : Adelic.BallNatural.Ball) (w : Adelic.BallGeometryData.ComplexPhase A) :
    ambientParameter A (baseParameter A) z.val w = Adelic.BallGeometryData.geometricFrame A z (Adelic.BallGeometryData.geometricCoordinates A w) := by
  funext v
  by_cases hv : v = A.distinguished
  · simp only [ambientParameter,Adelic.BallGeometryData.geometricFrame,Adelic.BallGeometryData.geometricCoordinates,ite_eq_left hv]
    apply Prod.ext
    · funext ij
      simp
    · funext ij
      simp
  · simp only [ambientParameter,Adelic.BallGeometryData.geometricFrame,Adelic.BallGeometryData.geometricCoordinates,ite_eq_right hv,baseParameter]
    apply Prod.ext
    · funext ij
      by_cases h : A.positive v ij.2 = true <;> simp [Matrix.diagonal_apply,h]
    · funext ij
      by_cases h : A.positive v ij.2 = true <;> simp [Matrix.diagonal_apply,h]

theorem geometricCoordinates_frame (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    Adelic.BallGeometryData.geometricCoordinates A (Adelic.BallGeometryData.geometricFrame A z a) = a := by
  funext q
  rcases q with ⟨v,i,j⟩
  by_cases hv : v = A.distinguished
  · fin_cases i <;> simp [Adelic.BallGeometryData.geometricCoordinates,Adelic.BallGeometryData.geometricFrame,hv,Adelic.DeterminantCoordinates.lineVector,Adelic.DeterminantCoordinates.annihilatorVector]
  · by_cases h : A.positive v j = true <;> simp [Adelic.BallGeometryData.geometricCoordinates,Adelic.BallGeometryData.geometricFrame,hv,h]

theorem ambientParameter_base_frame (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    ambientParameter A (baseParameter A) z.val (Adelic.BallGeometryData.geometricFrame A z a) = Adelic.BallGeometryData.geometricFrame A z a := by
  rw [ambientParameter_base,geometricCoordinates_frame]

def coordinateProjector (B : Adelic.DataTheta.ComparisonData F H K A) (p : ProjectorParameters A) (z : IntrinsicExterior.Intrinsic.Tangent) :
    Matrix (Sum (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A)) (Sum (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A)) ℂ :=
  fun i j => B.complexPhase.symm (ambientParameter A p z (B.complexPhase (Pi.single j 1))) i

theorem coordinateProjector_holomorphic (B : Adelic.DataTheta.ComparisonData F H K A) :
    Differentiable ℂ (fun q : ProjectorParameters A × IntrinsicExterior.Intrinsic.Tangent => coordinateProjector A B q.1 q.2) := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  exact (differentiable_apply i).comp (B.complexPhase.symm.differentiable.comp (ambientParameter_holomorphic A _))

end RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.Intrinsic

/-! The actual compact-frame choices give a continuous family of
idempotent projectors, based at the prescribed native Hodge projector. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

theorem change_continuous : Continuous (IntrinsicCompactChoices.Intrinsic.CompactFrameChoice.change (A := A)) :=
  continuous_induced_dom

theorem choice_parameter_continuous : Continuous (IntrinsicParameter.choiceParameter (A := A)) := by
  have hc := change_continuous A
  apply continuous_pi
  intro v
  have hv : Continuous (fun p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A => p.change v) :=
    (continuous_apply v).comp hc
  have hval : Continuous (fun p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A => (p.change v).val) :=
    Units.continuous_val.comp hv
  have hinv : Continuous (fun p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A => (p.change v).inv) :=
    Units.continuous_val.comp hv.inv
  have hvalT : Continuous (fun p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A => (p.change v).valᵀ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply i).comp ((continuous_apply j).comp hval)
  have hinvT : Continuous (fun p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A => (p.change v).invᵀ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply i).comp ((continuous_apply j).comp hinv)
  unfold IntrinsicParameter.choiceParameter
  apply Continuous.prodMk
  · exact (hval.mul continuous_const).mul hinv
  · exact (hinvT.mul continuous_const).mul hvalT

theorem choice_parameter_identity : IntrinsicParameter.choiceParameter A (IntrinsicCompactChoices.Intrinsic.identityChoice A) = IntrinsicParameter.baseParameter A := by
  funext v
  simp [IntrinsicParameter.choiceParameter,IntrinsicCompactChoices.Intrinsic.identityChoice]

theorem base_parameter_idempotent (v : Fin A.places) :
    (IntrinsicParameter.baseParameter A v).1 * (IntrinsicParameter.baseParameter A v).1 = (IntrinsicParameter.baseParameter A v).1 ∧
      (IntrinsicParameter.baseParameter A v).2 * (IntrinsicParameter.baseParameter A v).2 = (IntrinsicParameter.baseParameter A v).2 := by
  constructor <;> simp only [IntrinsicParameter.baseParameter,Matrix.diagonal_mul_diagonal]
  all_goals
    congr 1
    funext j
    split_ifs <;> simp

theorem conjugate_idempotent {I : Type} [Fintype I] [DecidableEq I]
    (U V P : Matrix I I ℂ) (hVU : V * U = 1) (hP : P * P = P) :
    (U * P * V) * (U * P * V) = U * P * V := by
  calc
    _ = U * P * (V * U) * P * V := by simp only [Matrix.mul_assoc]
    _ = U * P * P * V := by rw [hVU,Matrix.mul_one]
    _ = U * P * V := by rw [Matrix.mul_assoc U P P,hP]

theorem choice_parameter_idempotent (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (v : Fin A.places) :
    (IntrinsicParameter.choiceParameter A p v).1 * (IntrinsicParameter.choiceParameter A p v).1 = (IntrinsicParameter.choiceParameter A p v).1 ∧
      (IntrinsicParameter.choiceParameter A p v).2 * (IntrinsicParameter.choiceParameter A p v).2 = (IntrinsicParameter.choiceParameter A p v).2 := by
  constructor
  · exact conjugate_idempotent _ _ _ (p.change v).inv_val (base_parameter_idempotent A v).1
  · apply conjugate_idempotent _ _ _ _ (base_parameter_idempotent A v).2
    rw [← Matrix.transpose_mul,(p.change v).inv_val,Matrix.transpose_one]

end RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.Intrinsic

end

end OAI
