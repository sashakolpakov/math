import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Completion Compatible Equiv -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CompletionCompatibleEquiv.AnalyticLocal

noncomputable section

section

/-! Compatible maps on all finite quotients induce actual ring maps
on adic completions. -/

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

theorem completion_eval_transition {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on I R with
  | h a =>
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
    change Ideal.Quotient.mk (I ^ m) (a n) = Ideal.Quotient.mk (I ^ m) (a m)
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (a n) (a m)).mpr
    have ha := SModEq.sub_mem.mp (a.property h).symm
    have htop : (I ^ m • (⊤ : Submodule R R)) = I ^ m := Ideal.mul_top _
    rw [htop] at ha
    exact ha

theorem completion_family_compatible (f : ∀ n : ℕ, R ⧸ I ^ n →+* S ⧸ J ^ n)
    (hf : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow J h).comp (f n) = (f m).comp (Ideal.Quotient.factorPow I h)) :
    ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp
      ((f n).comp (AdicCompletion.evalₐ I n).toRingHom) =
        (f m).comp (AdicCompletion.evalₐ I m).toRingHom := by
  intro m n h
  ext x
  change Ideal.Quotient.factorPow J h (f n (AdicCompletion.evalₐ I n x)) = _
  calc
    _ = f m (Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x)) :=
      DFunLike.congr_fun (hf h) (AdicCompletion.evalₐ I n x)
    _ = _ := by rw [completion_eval_transition]; rfl

def completionCompatibleMap (f : ∀ n : ℕ, R ⧸ I ^ n →+* S ⧸ J ^ n)
    (hf : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow J h).comp (f n) = (f m).comp (Ideal.Quotient.factorPow I h)) :
    AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J (fun n => (f n).comp (AdicCompletion.evalₐ I n).toRingHom)
    (completion_family_compatible I J f hf)

theorem completionCompatibleMap_eval (f : ∀ n : ℕ, R ⧸ I ^ n →+* S ⧸ J ^ n)
    (hf : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow J h).comp (f n) = (f m).comp (Ideal.Quotient.factorPow I h))
    (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (completionCompatibleMap I J f hf x) = f n (AdicCompletion.evalₐ I n x) := by
  exact AdicCompletion.evalₐ_liftRingHom J _ (completion_family_compatible I J f hf) n x

end

/-! Compatible equivalences of finite quotients give an equivalence of
completions with the original quotient evaluations. -/

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
  (e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
  (he : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (e n).toRingHom =
    (e m).toRingHom.comp (Ideal.Quotient.factorPow I h))

include he in
theorem completion_inverse_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow I h).comp (e n).symm.toRingHom =
      (e m).symm.toRingHom.comp (Ideal.Quotient.factorPow J h) := by
  ext z
  apply (e m).injective
  change e m (Ideal.Quotient.factorPow I h ((e n).symm z)) =
    e m ((e m).symm (Ideal.Quotient.factorPow J h z))
  rw [(e m).apply_symm_apply]
  calc
    _ = Ideal.Quotient.factorPow J h (e n ((e n).symm z)) :=
      (DFunLike.congr_fun (he h) ((e n).symm z)).symm
    _ = _ := by rw [(e n).apply_symm_apply]

def completionCompatibleEquiv : AdicCompletion I R ≃+* AdicCompletion J S where
  __ := completionCompatibleMap I J (fun n => (e n).toRingHom) he
  invFun := completionCompatibleMap J I (fun n => (e n).symm.toRingHom)
    (completion_inverse_compatible I J e he)
  left_inv x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n
      (completionCompatibleMap J I (fun n => (e n).symm.toRingHom)
        (completion_inverse_compatible I J e he)
          (completionCompatibleMap I J (fun n => (e n).toRingHom) he x)) = _
    rw [completionCompatibleMap_eval, completionCompatibleMap_eval]
    exact (e n).symm_apply_apply _
  right_inv x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ J n
      (completionCompatibleMap I J (fun n => (e n).toRingHom) he
        (completionCompatibleMap J I (fun n => (e n).symm.toRingHom)
          (completion_inverse_compatible I J e he) x)) = _
    rw [completionCompatibleMap_eval, completionCompatibleMap_eval]
    exact (e n).apply_symm_apply _

theorem completionCompatibleEquiv_eval (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (completionCompatibleEquiv I J e he x) =
      e n (AdicCompletion.evalₐ I n x) := completionCompatibleMap_eval I J _ he n x

theorem completionCompatibleEquiv_of (f : R →+* S)
    (h : ∀ n : ℕ, ∀ r : R, e n (Ideal.Quotient.mk (I ^ n) r) = Ideal.Quotient.mk (J ^ n) (f r))
    (r : R) : completionCompatibleEquiv I J e he (AdicCompletion.of I R r) =
      AdicCompletion.of J S (f r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [completionCompatibleEquiv_eval, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, h]

def completionCompatibleAlgEquiv [Algebra R S]
    (h : ∀ n : ℕ, ∀ r : R, e n (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk (J ^ n) (algebraMap R S r)) :
    AdicCompletion I R ≃ₐ[R] AdicCompletion J S where
  __ := completionCompatibleEquiv I J e he
  commutes' r := completionCompatibleEquiv_of I J e he (algebraMap R S) h r

end

end OAI.AlgebraicGeometry.Comparison.Betti.CompletionCompatibleEquiv.AnalyticLocal
