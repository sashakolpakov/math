import OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality

/-! # Completion Maps -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CompletionMaps

noncomputable section

/-!
# Functorial maps of principal adic completions

These maps are defined directly on the compatible quotient rings, including
maps between different coefficient rings.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality

variable (p : ℕ) {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

def pAdicBetween (f : R →+* S) :
    AdicCompletion (Ideal.span {(p : R)}) R →+*
      AdicCompletion (Ideal.span {(p : S)}) S :=
  AdicCompletion.liftRingHom (Ideal.span {(p : S)})
    (Nontriviality.completionLiftComponent p f) (Nontriviality.completionLiftComponent_compatible p f)

@[simp]
theorem pAdicBetween_eval (f : R →+* S)
    (x : AdicCompletion (Ideal.span {(p : R)}) R) (n : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : S)}) n (pAdicBetween p f x) =
      Nontriviality.pPowerMapBetween p f n (AdicCompletion.evalₐ (Ideal.span {(p : R)}) n x) :=
  AdicCompletion.evalₐ_liftRingHom (Ideal.span {(p : S)})
    (Nontriviality.completionLiftComponent p f) (Nontriviality.completionLiftComponent_compatible p f) n x

@[simp]
theorem pAdicBetween_of (f : R →+* S) (x : R) :
    pAdicBetween p f (AdicCompletion.of (Ideal.span {(p : R)}) R x) =
      AdicCompletion.of (Ideal.span {(p : S)}) S (f x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [pAdicBetween_eval, AdicCompletion.evalₐ_of, Nontriviality.pPowerMapBetween_mk]

theorem pPowerMapBetween_id (n : ℕ) :
    Nontriviality.pPowerMapBetween p (RingHom.id R) n = RingHom.id _ := by
  apply RingHom.ext
  intro x
  induction x using Quotient.inductionOn' with
  | h x => rfl

theorem pPowerMapBetween_comp (f : R →+* S) (g : S →+* T) (n : ℕ) :
    Nontriviality.pPowerMapBetween p (g.comp f) n =
      (Nontriviality.pPowerMapBetween p g n).comp (Nontriviality.pPowerMapBetween p f n) := by
  apply RingHom.ext
  intro x
  induction x using Quotient.inductionOn' with
  | h x => rfl

theorem pAdicBetween_id : pAdicBetween p (RingHom.id R) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [pAdicBetween_eval, pPowerMapBetween_id]
  rfl

theorem pAdicBetween_comp (f : R →+* S) (g : S →+* T) :
    pAdicBetween p (g.comp f) = (pAdicBetween p g).comp (pAdicBetween p f) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ (Ideal.span {(p : T)}) n (pAdicBetween p (g.comp f) x) =
    AdicCompletion.evalₐ (Ideal.span {(p : T)}) n (pAdicBetween p g (pAdicBetween p f x))
  rw [pAdicBetween_eval, pAdicBetween_eval, pAdicBetween_eval, pPowerMapBetween_comp]
  rfl

theorem pAdicBetween_eq_pAdicMap (f : R →+* R) : pAdicBetween p f = PeriodRing.pAdicMap p f := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [pAdicBetween_eval, PeriodRing.pAdicMap_eval]
  rfl

def pAdicBetweenEquiv (e : R ≃+* S) :
    AdicCompletion (Ideal.span {(p : R)}) R ≃+*
      AdicCompletion (Ideal.span {(p : S)}) S :=
  { pAdicBetween p e.toRingHom with
    invFun := pAdicBetween p e.symm.toRingHom
    left_inv := fun x => by
      have h := pAdicBetween_comp p e.toRingHom e.symm.toRingHom
      have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
        ext y
        exact e.symm_apply_apply y
      rw [he, pAdicBetween_id] at h
      exact (DFunLike.congr_fun h x).symm
    right_inv := fun x => by
      have h := pAdicBetween_comp p e.symm.toRingHom e.toRingHom
      have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id S := by
        ext y
        exact e.apply_symm_apply y
      rw [he, pAdicBetween_id] at h
      exact (DFunLike.congr_fun h x).symm }

theorem pAdicBetween_natural (e : R →+* S) (f : R →+* R) (g : S →+* S)
    (h : ∀ x, e (f x) = g (e x))
    (x : AdicCompletion (Ideal.span {(p : R)}) R) :
    pAdicBetween p e (PeriodRing.pAdicMap p f x) = PeriodRing.pAdicMap p g (pAdicBetween p e x) := by
  have he : e.comp f = g.comp e := RingHom.ext h
  have hc := congrArg (pAdicBetween p) he
  rw [pAdicBetween_comp, pAdicBetween_comp, pAdicBetween_eq_pAdicMap,
    pAdicBetween_eq_pAdicMap] at hc
  exact DFunLike.congr_fun hc x

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CompletionMaps
