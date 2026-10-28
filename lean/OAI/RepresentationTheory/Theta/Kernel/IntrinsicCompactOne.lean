import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector

/-! # Intrinsic Compact One -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicMultiplicityPhase

/-! Actual standard and dual multiplicity actions on the native complex
trace tensor space. They commute with the action on the V factor. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

def multiplicityPhase (U V : Fin A.places → Matrix (Fin 2) (Fin 2) ℂ)
    (w : Adelic.BallGeometryData.ComplexPhase A) : Adelic.BallGeometryData.ComplexPhase A := fun v =>
  (fun ij => (U v).mulVec (fun r => (w v).1 (ij.1,r)) ij.2,
   fun ij => (V v).mulVec (fun r => (w v).2 (ij.1,r)) ij.2)

theorem multiplicity_phase_comp (U V U' V' : Fin A.places → Matrix (Fin 2) (Fin 2) ℂ)
    (w : Adelic.BallGeometryData.ComplexPhase A) :
    multiplicityPhase A U V (multiplicityPhase A U' V' w) =
      multiplicityPhase A (fun v => U v * U' v) (fun v => V v * V' v) w := by
  funext v
  apply Prod.ext
  · funext ij
    exact congrFun (Matrix.mulVec_mulVec (fun r => (w v).1 (ij.1,r)) (U v) (U' v)) ij.2
  · funext ij
    exact congrFun (Matrix.mulVec_mulVec (fun r => (w v).2 (ij.1,r)) (V v) (V' v)) ij.2

theorem multiplicity_phase_one (w : Adelic.BallGeometryData.ComplexPhase A) :
    multiplicityPhase A (fun _ => 1) (fun _ => 1) w = w := by
  funext v
  apply Prod.ext <;> funext ij <;> simp [multiplicityPhase]

def compactPhase (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) : Adelic.BallGeometryData.ComplexPhase A → Adelic.BallGeometryData.ComplexPhase A :=
  multiplicityPhase A (fun v => (p.change v).val) (fun v => (p.change v).invᵀ)

def compactPhaseInverse (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) : Adelic.BallGeometryData.ComplexPhase A → Adelic.BallGeometryData.ComplexPhase A :=
  multiplicityPhase A (fun v => (p.change v).inv) (fun v => (p.change v).valᵀ)

theorem compact_phase_left_inverse (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (w : Adelic.BallGeometryData.ComplexPhase A) :
    compactPhaseInverse A p (compactPhase A p w) = w := by
  unfold compactPhaseInverse compactPhase
  rw [multiplicity_phase_comp]
  have hv : (fun v => (p.change v).inv * (p.change v).val) = fun _ => 1 :=
    funext (fun v => (p.change v).inv_val)
  have ht : (fun v => (p.change v).valᵀ * (p.change v).invᵀ) = fun _ => 1 := by
    funext v
    rw [← Matrix.transpose_mul,(p.change v).inv_val,Matrix.transpose_one]
  rw [hv,ht,multiplicity_phase_one]

theorem compact_phase_right_inverse (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (w : Adelic.BallGeometryData.ComplexPhase A) :
    compactPhase A p (compactPhaseInverse A p w) = w := by
  unfold compactPhaseInverse compactPhase
  rw [multiplicity_phase_comp]
  have hv : (fun v => (p.change v).val * (p.change v).inv) = fun _ => 1 :=
    funext (fun v => (p.change v).val_inv)
  have ht : (fun v => (p.change v).invᵀ * (p.change v).valᵀ) = fun _ => 1 := by
    funext v
    rw [← Matrix.transpose_mul,(p.change v).val_inv,Matrix.transpose_one]
  rw [hv,ht,multiplicity_phase_one]

theorem multiplicity_phase_commutes (U V : Fin A.places → Matrix (Fin 2) (Fin 2) ℂ)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (w : Adelic.BallGeometryData.ComplexPhase A) :
    Adelic.BallGeometryData.geometricAction A g (multiplicityPhase A U V w) =
      multiplicityPhase A U V (Adelic.BallGeometryData.geometricAction A g w) := by
  funext v
  apply Prod.ext
  · funext ij
    simp only [Adelic.BallGeometryData.geometricAction,multiplicityPhase,Matrix.mulVec,dotProduct,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro k _
    ring
  · funext ij
    simp only [Adelic.BallGeometryData.geometricAction,multiplicityPhase,Matrix.mulVec,dotProduct,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro k _
    ring

def movingFrame (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) : Adelic.BallGeometryData.ComplexPhase A :=
  compactPhase A p (Adelic.BallGeometryData.geometricFrame A z a)

theorem moving_frame_equivariant (B : Adelic.DataTheta.ComparisonData F H K A) (hG : Adelic.DataTheta.GeometryIdentification B)
    (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (g : Adelic.RationalSU.ArchimedeanSU F H)
    (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    Adelic.BallGeometryData.geometricAction A g (movingFrame A p z a) =
      movingFrame A p (B.ball g • z) ((Adelic.BallGeometryData.frameMatrix A g z).mulVec a) := by
  unfold movingFrame compactPhase
  rw [multiplicity_phase_commutes,hG.2.2.2.2.2.2.2.2.1]

end RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicMultiplicityPhase

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicSignature

/-! The Hermitian-dual coordinate change attached to an actual compact
multiplicity choice follows from its unitary equation. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

def multiplicitySignature (v : Fin A.places) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun j => if A.positive v j then 1 else -1)

theorem multiplicity_form_signature (v : Fin A.places) :
    IntrinsicCompactChoices.Intrinsic.multiplicityForm A v = Complex.I • multiplicitySignature A v := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hp : A.positive v i <;> simp [IntrinsicCompactChoices.Intrinsic.multiplicityForm,multiplicitySignature,hp]
  · simp [IntrinsicCompactChoices.Intrinsic.multiplicityForm,multiplicitySignature,hij]

theorem choice_preserves_signature (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (v : Fin A.places) :
    (p.change v).val.conjTranspose * multiplicitySignature A v * (p.change v).val =
      multiplicitySignature A v := by
  have h := p.preserves v
  rw [multiplicity_form_signature,Matrix.mul_smul,Matrix.smul_mul] at h
  ext i j
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) h
  exact mul_left_cancel₀ Complex.I_ne_zero he

theorem signature_conjugate (v : Fin A.places) :
    (multiplicitySignature A v).map (starRingEnd ℂ) = multiplicitySignature A v := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hp : A.positive v i <;> simp [multiplicitySignature,hp]
  · simp [multiplicitySignature,hij]

theorem signature_inverse_conjugate (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (v : Fin A.places) :
    multiplicitySignature A v * (p.change v).inv.map (starRingEnd ℂ) =
      (p.change v).valᵀ * multiplicitySignature A v := by
  have h : (p.change v).val.conjTranspose * multiplicitySignature A v =
      multiplicitySignature A v * (p.change v).inv := by
    calc
      _ = ((p.change v).val.conjTranspose * multiplicitySignature A v * (p.change v).val) *
          (p.change v).inv := by rw [Matrix.mul_assoc,Matrix.mul_assoc,(p.change v).val_inv,Matrix.mul_one]
      _ = _ := by rw [choice_preserves_signature]
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.map (starRingEnd ℂ)) h
  have ht : (p.change v).val.conjTranspose.map (starRingEnd ℂ) = (p.change v).valᵀ := by
    ext i j
    exact star_star _
  rw [Matrix.map_mul,Matrix.map_mul,signature_conjugate,ht] at hc
  exact hc.symm

theorem signature_dual_change (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (v : Fin A.places)
    (x : Fin 2 → ℂ) :
    (fun i => (if A.positive v i then (1 : ℂ) else -1) *
      star ((p.change v).inv.mulVec x i)) =
    (p.change v).valᵀ.mulVec (fun i => (if A.positive v i then (1 : ℂ) else -1) * star (x i)) := by
  have hc : (fun i => star ((p.change v).inv.mulVec x i)) =
      ((p.change v).inv.map (starRingEnd ℂ)).mulVec (fun i => star (x i)) := by
    funext i
    change star (∑ j, (p.change v).inv i j * x j) = ∑ j, star ((p.change v).inv i j) * star (x j)
    simp only [star_sum,star_mul']
  have hm : (multiplicitySignature A v).mulVec (fun i => star ((p.change v).inv.mulVec x i)) =
      (p.change v).valᵀ.mulVec ((multiplicitySignature A v).mulVec (fun i => star (x i))) := by
    rw [hc,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,signature_inverse_conjugate]
  have hs (y : Fin 2 → ℂ) : (multiplicitySignature A v).mulVec y =
      fun i => (if A.positive v i then (1 : ℂ) else -1) * y i := by
    funext i
    exact Matrix.mulVec_diagonal _ y i
  rwa [hs,hs] at hm

end RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicSignature

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicTensorCoordinates

/-! Changing the compact multiplicity basis changes the actual real
tensor's standard and Hermitian-dual components by the inverse
multiplicity action. This identifies the physical coordinate change. -/

open scoped _root_.NumberField Classical _root_.Matrix Kronecker _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicMultiplicityPhase
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicSignature

theorem kronecker_multiplicity_change {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (M : Matrix I I ℂ) (N U : Matrix J J ℂ) (x : I × J → ℂ) (i : I) (j : J) :
    (M ⊗ₖ (U * N)).mulVec x (i,j) =
      U.mulVec (fun r => (M ⊗ₖ N).mulVec x (i,r)) j := by
  have hm : M ⊗ₖ (U * N) = ((1 : Matrix I I ℂ) ⊗ₖ U) * (M ⊗ₖ N) := by
    rw [← Matrix.mul_kronecker_mul,Matrix.one_mul]
  rw [hm,← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.one_apply]

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

theorem choice_real_standard (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (s : ∀ v : Fin A.places, Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 2)
    (v : Fin A.places) (i : Fin 3) (j : Fin 2) :
    (Adelic.BallGeometryData.realTensorComponents (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p) s v).1 (i,j) =
      (p.change v).inv.mulVec (fun r => (Adelic.BallGeometryData.realTensorComponents A s v).1 (i,r)) j := by
  change ((A.basisV v).inv ⊗ₖ ((p.change v).inv * (A.basisP v).inv)).mulVec
      (fun ij => A.complex v (s v ij)) (i,j) = _
  exact kronecker_multiplicity_change _ _ _ _ i j

theorem choice_real_tensor (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (s : ∀ v : Fin A.places, Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 2) :
    Adelic.BallGeometryData.realTensorComponents (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p) s = IntrinsicMultiplicityPhase.compactPhaseInverse A p (Adelic.BallGeometryData.realTensorComponents A s) := by
  funext v
  apply Prod.ext
  · funext ij
    exact choice_real_standard A p s v ij.1 ij.2
  · funext ij
    rcases ij with ⟨i,j⟩
    let x : Fin 2 → ℂ := fun r => ((A.basisV v).inv ⊗ₖ (A.basisP v).inv).mulVec
      (fun kl => A.complex v (s v kl)) (i,r)
    have hs : ((A.basisV v).inv ⊗ₖ (A.basisP v * p.change v).inv).mulVec
        (fun kl => A.complex v (s v kl)) (i,j) = (p.change v).inv.mulVec x j :=
      choice_real_standard A p s v i j
    dsimp only [Adelic.BallGeometryData.realTensorComponents,IntrinsicMultiplicityPhase.compactPhaseInverse,IntrinsicMultiplicityPhase.multiplicityPhase,IntrinsicCompactChoices.Intrinsic.choiceArithmetic]
    rw [hs]
    have hd := congrFun (IntrinsicSignature.signature_dual_change A p v x) j
    rw [mul_assoc,hd]
    dsimp only [x]
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring

end RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicTensorCoordinates

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicCoordinateAgreement

/-! The compact multiplicity change and the native real/rational
phase coordinates describe the same physical tensor. The agreement
holds for the full native comparison data, without aligning their
rational coordinates by assumption. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicMultiplicityPhase OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicTensorCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem comparison_real_components (B : Adelic.DataTheta.ComparisonData F H K A)
    (hC : Adelic.DataTheta.CoordinateIdentification B P) (x : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    B.complexPhase (fun i => (B.realPhase x i : ℂ)) =
      Adelic.BallGeometryData.realTensorComponents A (fun v =>
        ((P.localFrame (.inl (A.enumerate v))).coordinates).symm
          (fun j => (A.real v).symm (x v j))) := by
  let s := fun v => ((P.localFrame (.inl (A.enumerate v))).coordinates).symm
    (fun j => (A.real v).symm (x v j))
  have h := hC.2.2.2.2.2.2.1 s
  have hs : (fun v j => A.real v ((P.localFrame (.inl (A.enumerate v))).coordinates (s v) j)) = x := by
    funext v j
    change A.real v (((P.localFrame (.inl (A.enumerate v))).coordinates)
      (((P.localFrame (.inl (A.enumerate v))).coordinates).symm
        (fun k => (A.real v).symm (x v k))) j) = x v j
    rw [LinearEquiv.apply_symm_apply,RingEquiv.apply_symm_apply]
  rw [hs] at h
  exact h

theorem compact_comparison_real (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (B : Adelic.DataTheta.ComparisonData F H K A) (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
    (hC : Adelic.DataTheta.CoordinateIdentification B P) (hCp : Adelic.DataTheta.CoordinateIdentification Bp P)
    (x : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    Bp.complexPhase (fun i => (Bp.realPhase x i : ℂ)) =
      IntrinsicMultiplicityPhase.compactPhaseInverse A p (B.complexPhase (fun i => (B.realPhase x i : ℂ))) := by
  exact (comparison_real_components Bp hCp x).trans
    ((IntrinsicTensorCoordinates.choice_real_tensor A p _).trans
      (congrArg (IntrinsicMultiplicityPhase.compactPhaseInverse A p) (comparison_real_components B hC x).symm))

theorem compact_comparison_rational (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (B : Adelic.DataTheta.ComparisonData F H K A) (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
    (hC : Adelic.DataTheta.CoordinateIdentification B P) (hCp : Adelic.DataTheta.CoordinateIdentification Bp P)
    (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F 6) :
    Bp.complexPhase (fun i => (Bp.rationalPhase x i : ℂ)) =
      IntrinsicMultiplicityPhase.compactPhaseInverse A p (B.complexPhase (fun i => (B.rationalPhase x i : ℂ))) := by
  let u := fun v j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j))
  have h := compact_comparison_real p B Bp hC hCp u
  have hB : B.complexPhase (fun i => (B.realPhase u i : ℂ)) =
      B.complexPhase (fun i => (B.rationalPhase x i : ℂ)) := by
    apply congrArg B.complexPhase
    funext i
    exact (congrArg Complex.ofReal (hC.2.2.2.1 x i)).trans (Complex.ofReal_ratCast _)
  have hp : Bp.complexPhase (fun i => (Bp.realPhase u i : ℂ)) =
      Bp.complexPhase (fun i => (Bp.rationalPhase x i : ℂ)) := by
    apply congrArg Bp.complexPhase
    funext i
    exact (congrArg Complex.ofReal (hCp.2.2.2.1 x i)).trans (Complex.ofReal_ratCast _)
  exact hp.symm.trans (h.trans (congrArg (IntrinsicMultiplicityPhase.compactPhaseInverse A p) hB))

end RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicCoordinateAgreement

end

end OAI
