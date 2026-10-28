import OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality

/-! # Additive Completion -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.AdditiveCompletion

noncomputable section

/-!
# Additive maps between p-adic completions of rings

An additive map preserves multiplication by integers, so it induces maps on
all p-power quotients and on their inverse limits. No multiplicativity of the
original map is needed.
-/

section Quotients

variable (p : ℕ) {R S : Type*} [CommRing R] [CommRing S]

/-- An additive map descends through the p-power ideals. -/
def quotientAddMap (f : R →+ S) (n : ℕ) :
    R ⧸ (Ideal.span {(p : R)}) ^ n →+ S ⧸ (Ideal.span {(p : S)}) ^ n :=
  QuotientAddGroup.lift ((Ideal.span {(p : R)}) ^ n).toAddSubgroup
    ((Ideal.Quotient.mk _).toAddMonoidHom.comp f) (by
      intro a ha
      change Ideal.Quotient.mk ((Ideal.span {(p : S)}) ^ n) (f a) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change a ∈ (Ideal.span {(p : R)}) ^ n at ha
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha ⊢
      obtain ⟨b, rfl⟩ := ha
      refine ⟨f b, ?_⟩
      have h := f.map_nsmul (p ^ n) b
      simpa only [nsmul_eq_mul, Nat.cast_pow] using h)

theorem quotientAddMap_mk (f : R →+ S) (n : ℕ) (a : R) :
    quotientAddMap p f n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f a) := rfl

theorem quotientAddMap_factor (f : R →+ S) {m n : ℕ} (h : m ≤ n)
    (x : R ⧸ (Ideal.span {(p : R)}) ^ n) :
    Ideal.Quotient.factorPow (Ideal.span {(p : S)}) h (quotientAddMap p f n x) =
      quotientAddMap p f m (Ideal.Quotient.factorPow (Ideal.span {(p : R)}) h x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end Quotients

section Lift

variable {A S : Type*} [AddCommGroup A] [CommRing S] (I : Ideal S)

/-- Compatible additive maps into the defining quotients give a map to completion. -/
def liftAddHom (f : (n : ℕ) → A →+ S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (h : m ≤ n) (x : A),
      Ideal.Quotient.factorPow I h (f n x) = f m x) : A →+ AdicCompletion I S where
  toFun x := ⟨fun n => Ideal.Quotient.factor (le_of_eq (Ideal.mul_top _).symm) (f n x),
    fun hkl => by
      dsimp only
      rw [← hf hkl x]
      generalize f _ x = q
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      rfl⟩
  map_zero' := by
    apply AdicCompletion.ext
    intro n
    simp only [map_zero]
    rfl
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    simp only [map_add]
    rfl

theorem liftAddHom_eval (f : (n : ℕ) → A →+ S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (h : m ≤ n) (x : A),
      Ideal.Quotient.factorPow I h (f n x) = f m x) (n : ℕ) (x : A) :
    AdicCompletion.evalₐ I n (liftAddHom I f hf x) = f n x := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top _))]
  have hh : Submodule.factor (le_of_eq (Ideal.mul_top (I ^ n)))
      (Ideal.Quotient.factor (le_of_eq (Ideal.mul_top (I ^ n)).symm) (f n x)) = f n x := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (f n x)
    rw [← ha]
    rfl
  exact hh

end Lift

variable (p : ℕ) {R S : Type*} [CommRing R] [CommRing S]

theorem completionAddMap_compatible (f : R →+ S) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion (Ideal.span {(p : R)}) R) :
    Ideal.Quotient.factorPow (Ideal.span {(p : S)}) h
        (quotientAddMap p f n (AdicCompletion.evalₐ (Ideal.span {(p : R)}) n x)) =
      quotientAddMap p f m (AdicCompletion.evalₐ (Ideal.span {(p : R)}) m x) := by
  rw [quotientAddMap_factor, PeriodRing.completionEval_factorPow]

def completionAddMap (f : R →+ S) :
    AdicCompletion (Ideal.span {(p : R)}) R →+
      AdicCompletion (Ideal.span {(p : S)}) S :=
  liftAddHom (Ideal.span {(p : S)})
    (fun n => (quotientAddMap p f n).comp
      (AdicCompletion.evalₐ (Ideal.span {(p : R)}) n).toAddMonoidHom)
    (completionAddMap_compatible p f)

theorem completionAddMap_eval (f : R →+ S)
    (x : AdicCompletion (Ideal.span {(p : R)}) R) (n : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : S)}) n (completionAddMap p f x) =
      quotientAddMap p f n (AdicCompletion.evalₐ (Ideal.span {(p : R)}) n x) :=
  liftAddHom_eval _ _ (completionAddMap_compatible p f) n x

theorem completionAddMap_of (f : R →+ S) (a : R) :
    completionAddMap p f (AdicCompletion.of (Ideal.span {(p : R)}) R a) =
      AdicCompletion.of (Ideal.span {(p : S)}) S (f a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [completionAddMap_eval, AdicCompletion.evalₐ_of,
    quotientAddMap_mk, AdicCompletion.evalₐ_of]

theorem completionAddMap_scaled_mul (f : R →+ S) (c : ℕ)
    (hf : ∀ a b : R, (c : S) * f (a * b) = f a * f b)
    (x y : AdicCompletion (Ideal.span {(p : R)}) R) :
    (c : AdicCompletion (Ideal.span {(p : S)}) S) * completionAddMap p f (x * y) =
      completionAddMap p f x * completionAddMap p f y := by
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [map_mul, map_natCast, completionAddMap_eval]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (Ideal.span {(p : R)}) n x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (Ideal.span {(p : R)}) n y)
  rw [← ha, ← hb, ← map_mul, quotientAddMap_mk, quotientAddMap_mk, quotientAddMap_mk]
  have h := congrArg (Ideal.Quotient.mk ((Ideal.span {(p : S)}) ^ n)) (hf a b)
  simp only [map_mul, map_natCast] at h
  exact h

variable [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- Extend an additive map into a p-adically complete ring. -/
def extendAddMap (f : R →+ S) : AdicCompletion (Ideal.span {(p : R)}) R →+ S :=
  (AdicCompletion.ofAlgEquiv (Ideal.span {(p : S)})).symm.toAddMonoidHom.comp
    (completionAddMap p f)

theorem extendAddMap_of (f : R →+ S) (a : R) :
    extendAddMap p f (AdicCompletion.of (Ideal.span {(p : R)}) R a) = f a := by
  change (AdicCompletion.ofAlgEquiv _).symm (completionAddMap p f _) = _
  rw [completionAddMap_of, AdicCompletion.ofAlgEquiv_symm_of]

theorem extendAddMap_eval (f : R →+ S)
    (x : AdicCompletion (Ideal.span {(p : R)}) R) (n : ℕ) :
    Ideal.Quotient.mk ((Ideal.span {(p : S)}) ^ n) (extendAddMap p f x) =
      quotientAddMap p f n (AdicCompletion.evalₐ (Ideal.span {(p : R)}) n x) := by
  change Ideal.Quotient.mk _ ((AdicCompletion.ofAlgEquiv _).symm
    (completionAddMap p f x)) = _
  rw [AdicCompletion.mk_ofAlgEquiv_symm, completionAddMap_eval]

theorem extendAddMap_scaled_mul (f : R →+ S) (c : ℕ)
    (hf : ∀ a b : R, (c : S) * f (a * b) = f a * f b)
    (x y : AdicCompletion (Ideal.span {(p : R)}) R) :
    (c : S) * extendAddMap p f (x * y) = extendAddMap p f x * extendAddMap p f y := by
  have h := congrArg (AdicCompletion.ofAlgEquiv (Ideal.span {(p : S)})).symm
    (completionAddMap_scaled_mul p f c hf x y)
  simp only [map_mul, map_natCast] at h
  exact h

theorem extendAddMap_scaled_natural {T : Type*} [CommRing T]
    [IsAdicComplete (Ideal.span {(p : T)}) T]
    (f : R →+ S) (g : R →+ T) (e : S →+ T) (a b : ℕ)
    (he : ∀ r : R, (a : T) * e (f r) = (b : T) * g r)
    (x : AdicCompletion (Ideal.span {(p : R)}) R) :
    (a : T) * e (extendAddMap p f x) = (b : T) * extendAddMap p g x := by
  apply AdicCompletion.of_injective (Ideal.span {(p : T)}) T
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
  simp only [map_mul, map_natCast]
  rw [← quotientAddMap_mk p e n, extendAddMap_eval, extendAddMap_eval]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (Ideal.span {(p : R)}) n x)
  rw [← hr, quotientAddMap_mk, quotientAddMap_mk, quotientAddMap_mk]
  have h := congrArg (Ideal.Quotient.mk ((Ideal.span {(p : T)}) ^ n)) (he r)
  simpa only [map_mul, map_natCast] using h

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.AdditiveCompletion
