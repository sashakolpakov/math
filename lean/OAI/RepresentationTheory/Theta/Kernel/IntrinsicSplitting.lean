import OAI.RepresentationTheory.Theta.OneFormsIntrinsicOf
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior

/-! # Intrinsic Splitting -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands

/-! Two actual multiplicity-one ThetaOneForms constructions in common V coordinates.
Only arithmetic skew-Hermitian data are inputs. All native AdelicTheta and ThetaOneForms
conclusions are retained for the constructed witnesses. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.Data OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection OAI.RepresentationTheory.Theta.OneFormsIntrinsicOf.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}

/-- Arithmetic orthonormal coordinates for the second multiplicity line,
using exactly the same CM embeddings and V basis as the first line. -/
structure SecondLine (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁) where
  form : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ
  skewHermitian : form.val.conjTranspose = -form.val
  basis : Fin A.places → (Matrix (Fin 1) (Fin 1) ℂ)ˣ
  positive : Fin A.places → Fin 1 → Bool
  distinguished_sign : ∀ j, positive A.distinguished j = false
  normalized : ∀ v,
    (basis v).val.conjTranspose *
      ((Weil.AdelicSplitting.Integral.Construction.localizedForm F form.val (.inl (A.enumerate v))).map (A.complex v)) * (basis v).val =
        Matrix.diagonal (fun j => if positive v j then Complex.I else -Complex.I)

abbrev secondArithmetic (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁) (S : SecondLine A) :
    Adelic.BallGeometryData.BallArithmeticData F d 1 H S.form where
  places := A.places
  enumerate := A.enumerate
  distinguished := A.distinguished
  other_place := A.other_place
  real := A.real
  real_continuous := A.real_continuous
  real_inverse_continuous := A.real_inverse_continuous
  complex := A.complex
  complex_continuous := A.complex_continuous
  complex_inverse_continuous := A.complex_inverse_continuous
  complex_scalar := A.complex_scalar
  complex_star := A.complex_star
  basisV := A.basisV
  basisP := S.basis
  positive := S.positive
  distinguished_sign := S.distinguished_sign
  formV := A.formV
  formP := S.normalized

structure SummandWitnesses
    (K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ) (hd : d ≠ 0)
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K) (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K) where
  characters : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 1
  splittings : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 1 H K hd characters P
  comparison : Adelic.DataTheta.ComparisonData F H K A

def SummandValid
    {K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ} {hd : d ≠ 0}
    {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K} {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K}
    (Q : SummandWitnesses K hd P A) (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) : Prop :=
  Q.characters.ψ = ψ ∧ Adelic.Data.CharacterConclusion F d 3 1 Q.characters ∧
  Adelic.Data.AdelicConclusion F d 3 1 H K hd Q.characters P Q.splittings ∧
  Adelic.Data.FiniteConclusion F d 3 1 H K hd Q.characters P Q.splittings ∧
  Adelic.DataTheta.CoordinateIdentification Q.comparison P ∧ Adelic.DataTheta.GeometryIdentification Q.comparison ∧
  Adelic.DataTheta.OscillatorIdentification Q.comparison P hd Q.characters Q.splittings ∧
  Adelic.SiegelBranchData.SiegelBranchExtension Q.comparison P hd Q.characters Q.splittings ∧
  Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd Q.characters Q.splittings ∧ Adelic.DataTheta.Descent.ThetaConstruction Q.comparison ∧
  Adelic.DataTheta.Descent.RationalHeckeCovariance Q.comparison P hd Q.characters Q.splittings ∧
  Adelic.DataTheta.Descent.CongruenceDescent Q.comparison P hd Q.characters Q.splittings ∧
  OneFormsIntrinsicOf.Intrinsic.NativeConclusion Q.comparison P hd Q.characters Q.splittings

theorem construct_summand (h_AdelicTheta : Adelic.Data.CompleteStatement)
    (hq : d ≠ 0 ∧ ¬ IsSquare d)
    (K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
    (hn : ∃ x, ψ x ≠ 1) (hp : ∀ x : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) x) = 1)
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K) (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K)
    (hArch : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ) :
    ∃ Q : SummandWitnesses K hq.1 P A, SummandValid Q ψ := by
  obtain ⟨C, hψ, hChar, D, hAd, hFin, B, hCoord, hGeom, hOsc, hBranch,
      hUnique, hTheta, hCov, hDesc, hNative⟩ :=
    OneFormsIntrinsicOf.Intrinsic.theta_one_forms_of_complete_AdelicTheta h_AdelicTheta F d hq H K hH hK ψ hc hu hn hp P A hArch
  exact ⟨⟨C, D, B⟩, hψ, hChar, hAd, hFin, hCoord, hGeom, hOsc,
    hBranch, hUnique, hTheta, hCov, hDesc, hNative⟩

theorem same_ball_action (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁) (S : SecondLine A)
    (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A) (B₂ : Adelic.DataTheta.ComparisonData F H S.form (secondArithmetic A S))
    (h₁ : Adelic.DataTheta.GeometryIdentification B₁) (h₂ : Adelic.DataTheta.GeometryIdentification B₂) :
    B₁.ball = B₂.ball := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply Units.ext
  exact (h₁.2.1 g).trans (h₂.2.1 g).symm

theorem construct_two_summands (h_AdelicTheta : Adelic.Data.CompleteStatement)
    (hq : d ≠ 0 ∧ ¬ IsSquare d)
    (hH : H.val.conjTranspose = H.val) (hK₁ : K₁.val.conjTranspose = -K₁.val)
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
    (hn : ∃ x, ψ x ≠ 1) (hp : ∀ x : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) x) = 1)
    (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁) (S : SecondLine A)
    (P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁) (P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form)
    (hArch : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ) :
    ∃ (Q₁ : SummandWitnesses K₁ hq.1 P₁ A)
      (Q₂ : SummandWitnesses S.form hq.1 P₂ (secondArithmetic A S)),
      SummandValid Q₁ ψ ∧ SummandValid Q₂ ψ ∧ Q₁.comparison.ball = Q₂.comparison.ball := by
  obtain ⟨Q₁, h₁⟩ := construct_summand h_AdelicTheta hq K₁ hH hK₁ ψ hc hu hn hp P₁ A hArch
  obtain ⟨Q₂, h₂⟩ := construct_summand h_AdelicTheta hq S.form hH S.skewHermitian ψ hc hu hn hp
    P₂ (secondArithmetic A S) hArch
  exact ⟨Q₁, Q₂, h₁, h₂,
    same_ball_action A S Q₁.comparison Q₂.comparison h₁.2.2.2.2.2.1 h₂.2.2.2.2.2.1⟩

end RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands

namespace RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic

/-! The orthogonal sum of the two actual multiplicity lines, including
its CM orthonormal bases and signatures. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands

def blockUnit {R : Type*} [Semiring R]
    (a b : (Matrix (Fin 1) (Fin 1) R)ˣ) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := Matrix.diagonal ![a.val 0 0, b.val 0 0]
  inv := Matrix.diagonal ![a.inv 0 0, b.inv 0 0]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_succ] using
        congrArg (fun M : Matrix (Fin 1) (Fin 1) R => M 0 0) a.val_inv
    · simp
    · simp
    · simpa [Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_succ] using
        congrArg (fun M : Matrix (Fin 1) (Fin 1) R => M 0 0) b.val_inv
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_succ] using
        congrArg (fun M : Matrix (Fin 1) (Fin 1) R => M 0 0) a.inv_val
    · simp
    · simp
    · simpa [Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_succ] using
        congrArg (fun M : Matrix (Fin 1) (Fin 1) R => M 0 0) b.inv_val

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}

omit [NumberField F] in
theorem blockUnit_skewHermitian
    (K₂ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (h₁ : K₁.val.conjTranspose = -K₁.val) (h₂ : K₂.val.conjTranspose = -K₂.val) :
    (blockUnit K₁ K₂).val.conjTranspose = -(blockUnit K₁ K₂).val := by
  have ha := congrArg (fun M : Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) => M 0 0) h₁
  have hb := congrArg (fun M : Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) => M 0 0) h₂
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [blockUnit, Matrix.conjTranspose_apply] using ha
  · simp [blockUnit]
  · simp [blockUnit]
  · simpa [blockUnit, Matrix.conjTranspose_apply] using hb

abbrev sumArithmetic (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁) (S : IntrinsicSummands.SecondLine A) :
    Adelic.BallGeometryData.BallArithmeticData F d 2 H (blockUnit K₁ S.form) where
  places := A.places
  enumerate := A.enumerate
  distinguished := A.distinguished
  other_place := A.other_place
  real := A.real
  real_continuous := A.real_continuous
  real_inverse_continuous := A.real_inverse_continuous
  complex := A.complex
  complex_continuous := A.complex_continuous
  complex_inverse_continuous := A.complex_inverse_continuous
  complex_scalar := A.complex_scalar
  complex_star := A.complex_star
  basisV := A.basisV
  basisP := fun v => blockUnit (A.basisP v) (S.basis v)
  positive := fun v => ![A.positive v 0, S.positive v 0]
  distinguished_sign := by intro j; fin_cases j <;> simp [A.distinguished_sign, S.distinguished_sign]
  formV := A.formV
  formP := by
    intro v
    have ha := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) (A.formP v)
    have hb := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) (S.normalized v)
    simp [Matrix.mul_apply, Weil.AdelicSplitting.Integral.Construction.localizedForm] at ha hb
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [blockUnit, Matrix.mul_apply, Fin.sum_univ_succ, Weil.AdelicSplitting.Integral.Construction.localizedForm,
        ha, hb]
    all_goals rfl

end RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic

namespace RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicFrames

/-! Explicit rational and local symplectic coordinates for the orthogonal
sum. Pairings are checked on the actual trace tensor space. -/

open scoped Classical _root_.Matrix Kronecker

open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic

variable {k : Type} [Field k] {d : k}

def tensorSplit : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 2 ≃ₗ[k]
    Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1 × Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 1 where
  toFun x := (fun i => x (i.1, 0), fun i => x (i.1, 1))
  invFun p i := if i.2 = 0 then p.1 (i.1, 0) else p.2 (i.1, 0)
  left_inv x := by funext i; rcases i with ⟨i,j⟩; fin_cases j <;> rfl
  right_inv p := by
    apply Prod.ext <;> funext i <;> rcases i with ⟨i,j⟩ <;> fin_cases j <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def phaseIndex : ((Fin 3 ⊕ Fin 3) ⊕ (Fin 3 ⊕ Fin 3)) ≃ (Fin 6 ⊕ Fin 6) :=
  (Equiv.sumSumSumComm (Fin 3) (Fin 3) (Fin 3) (Fin 3)).trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

def phaseSplit : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) 3 2 ≃ₗ[k]
    Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) 3 1 × Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) 3 1 :=
  (LinearEquiv.piCongrLeft k (fun _ : Fin 6 ⊕ Fin 6 => k) phaseIndex).symm.trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k k)

theorem phaseSplit_left (x : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) 3 2) :
    (phaseSplit x).1 = Sum.elim (fun i => x (.inl (Fin.castAdd 3 i)))
      (fun i => x (.inr (Fin.castAdd 3 i))) := by
  funext i
  rcases i with i | i <;> rfl

theorem phaseSplit_right (x : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) 3 2) :
    (phaseSplit x).2 = Sum.elim (fun i => x (.inl (Fin.natAdd 3 i)))
      (fun i => x (.inr (Fin.natAdd 3 i))) := by
  funext i
  rcases i with i | i <;> rfl

theorem phaseSplit_symm (x y : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) 3 1) :
    phaseSplit.symm (x,y) = Sum.elim
      (Fin.append (fun i => x (.inl i)) (fun i => y (.inl i)))
      (Fin.append (fun i => x (.inr i)) (fun i => y (.inr i))) := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

theorem phaseSplit_pairing (x y : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) 3 2) :
    Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 2 x y =
      Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 1 (phaseSplit x).1 (phaseSplit y).1 +
      Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 1 (phaseSplit x).2 (phaseSplit y).2 := by
  simp [Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing, Matrix.J, Matrix.toBilin'_apply,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply, Fin.sum_univ_succ,
    phaseSplit_left, phaseSplit_right]
  ring

theorem tensorSplit_formValue (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (K₁ K₂ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (x y : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 2) :
    Weil.AdelicSplitting.TensorSpace.Construction.formValue (H ⊗ₖ (IntrinsicArithmetic.blockUnit K₁ K₂).val) x y =
      Weil.AdelicSplitting.TensorSpace.Construction.formValue (H ⊗ₖ K₁.val) (tensorSplit x).1 (tensorSplit y).1 +
      Weil.AdelicSplitting.TensorSpace.Construction.formValue (H ⊗ₖ K₂.val) (tensorSplit x).2 (tensorSplit y).2 := by
  simp [Weil.AdelicSplitting.TensorSpace.Construction.formValue, IntrinsicArithmetic.blockUnit, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_two, tensorSplit, Finset.sum_add_distrib]

theorem tensorSplit_pairing (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (K₁ K₂ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (x y : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 2) :
    Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d 3 2 H (IntrinsicArithmetic.blockUnit K₁ K₂).val x y =
      Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d 3 1 H K₁.val (tensorSplit x).1 (tensorSplit y).1 +
      Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d 3 1 H K₂.val (tensorSplit x).2 (tensorSplit y).2 := by
  unfold Weil.AdelicSplitting.TensorSpace.Construction.tracePairing
  rw [tensorSplit_formValue, map_add, add_div]

def sumFrame (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (K₁ K₂ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (P₁ : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d 3 1 H K₁.val) (P₂ : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d 3 1 H K₂.val) :
    Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d 3 2 H (IntrinsicArithmetic.blockUnit K₁ K₂).val where
  coordinates := tensorSplit.trans ((P₁.coordinates.prodCongr P₂.coordinates).trans phaseSplit.symm)
  preserves x y := by
    rw [phaseSplit_pairing]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.prodCongr_apply]
    rw [P₁.preserves, P₂.preserves, tensorSplit_pairing]

end RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicFrames

namespace RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal

/-! The sum symplectic frame is compatible with every localization of
the rational trace tensor space. -/

open scoped _root_.NumberField Classical _root_.Matrix

open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicFrames

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ K₂ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}

theorem localized_blockUnit (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d (IntrinsicArithmetic.blockUnit K₁ K₂) v).val =
      (IntrinsicArithmetic.blockUnit (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K₁ v) (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K₂ v)).val := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [IntrinsicArithmetic.blockUnit, Weil.AdelicSplitting.Assembly.Construction.localizedUnit]

def sumGlobalFrames (P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁) (P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₂) :
    Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H (IntrinsicArithmetic.blockUnit K₁ K₂) where
  rational := IntrinsicFrames.sumFrame H.val K₁ K₂ P₁.rational P₂.rational
  localFrame v :=
    { coordinates := IntrinsicFrames.tensorSplit.trans
        (((P₁.localFrame v).coordinates.prodCongr (P₂.localFrame v).coordinates).trans IntrinsicFrames.phaseSplit.symm)
      preserves := by
        intro x y
        rw [localized_blockUnit]
        exact (IntrinsicFrames.sumFrame (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d H v).val
          (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K₁ v) (Weil.AdelicSplitting.Assembly.Construction.localizedUnit F d K₂ v)
          (P₁.localFrame v) (P₂.localFrame v)).preserves x y }
  coordinates_compatible := by
    intro v x i
    change IntrinsicFrames.phaseSplit.symm
      ((P₁.localFrame v).coordinates (IntrinsicFrames.tensorSplit (fun j => Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v (x j))).1,
       (P₂.localFrame v).coordinates (IntrinsicFrames.tensorSplit (fun j => Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v (x j))).2) i =
      Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v (IntrinsicFrames.phaseSplit.symm
        (P₁.rational.coordinates (IntrinsicFrames.tensorSplit x).1, P₂.rational.coordinates (IntrinsicFrames.tensorSplit x).2) i)
    rw [IntrinsicFrames.phaseSplit_symm, IntrinsicFrames.phaseSplit_symm]
    rcases i with i | i <;> fin_cases i
    all_goals
      first
      | exact P₁.coordinates_compatible v (IntrinsicFrames.tensorSplit x).1 _
      | exact P₂.coordinates_compatible v (IntrinsicFrames.tensorSplit x).2 _

end RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal

end

end OAI
