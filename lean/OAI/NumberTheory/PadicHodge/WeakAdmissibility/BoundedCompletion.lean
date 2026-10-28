import Mathlib

/-! # Bounded Completion -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion

/-!
Extension of additive maps through p-adic completion, with a uniform
denominator bound. The bound is a property to be proved for each concrete map.
-/

section AdditiveLift
variable {A R : Type*} [AddCommGroup A] [CommRing R] (I : Ideal R)
variable (f : (n : ℕ) → A →+ R ⧸ I ^ n)
  (hf : ∀ {m n : ℕ} (h : m ≤ n),
    (Ideal.Quotient.factorPow I h).toAddMonoidHom.comp (f n) = f m)

def adicLiftAddHom : A →+ AdicCompletion I R where
  toFun x := ⟨fun n => Ideal.Quotient.factor (le_of_eq (Ideal.mul_top _).symm) (f n x), by
    intro m n h
    simp only [AdicCompletion.transitionMap, Submodule.factorPow]
    have he := DFunLike.congr_fun (hf h) x
    change Ideal.Quotient.factorPow I h (f n x) = f m x at he
    generalize f n x = a at he ⊢
    rw [← he]
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl⟩
  map_zero' := by ext n; simp
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    change Ideal.Quotient.factor _ (f n (x + y)) =
      Ideal.Quotient.factor _ (f n x) + Ideal.Quotient.factor _ (f n y)
    rw [map_add, map_add]

theorem eval_adicLiftAddHom (n : ℕ) (x : A) :
    AdicCompletion.evalₐ I n (adicLiftAddHom I f hf x) = f n x := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top _))]
  change Ideal.Quotient.factor (le_of_eq (Ideal.mul_top _))
    (Ideal.Quotient.factor (le_of_eq (Ideal.mul_top _).symm) (f n x)) = _
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (f n x)
  rw [← ha]
  rfl

end AdditiveLift

theorem eq_of_quotient_eq {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {x y : R} (h : ∀ n : ℕ, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) : x = y := by
  apply (AdicCompletion.ofAlgEquiv I).injective
  apply AdicCompletion.ext_evalₐ
  intro n
  simpa only [AdicCompletion.ofAlgEquiv_apply, AdicCompletion.evalₐ_of] using h n

section ScaledMap
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
variable (p C : ℕ) (j : R →+* S) (hj : Function.Injective j) (f : A →+* S)
variable (hb : ∀ a : A, ∃ r : R, j r = (p : S) ^ C * f a)

def scaledLift : A →+ R where
  toFun a := (hb a).choose
  map_zero' := hj (by rw [(hb 0).choose_spec, map_zero, mul_zero, map_zero])
  map_add' a b := hj (by
    rw [(hb (a + b)).choose_spec, map_add, map_add,
      (hb a).choose_spec, (hb b).choose_spec, mul_add])

theorem scaledLift_spec (a : A) :
    j (scaledLift p C j hj f hb a) = (p : S) ^ C * f a := (hb a).choose_spec

theorem scaledLift_nat_mul (n : ℕ) (a : A) :
    scaledLift p C j hj f hb ((n : A) * a) = (n : R) * scaledLift p C j hj f hb a := by
  simpa only [nsmul_eq_mul] using (scaledLift p C j hj f hb).map_nsmul n a

theorem scaledLift_mul (a b : A) :
    (p : R) ^ C * scaledLift p C j hj f hb (a * b) =
      scaledLift p C j hj f hb a * scaledLift p C j hj f hb b := by
  apply hj
  simp only [map_mul, map_pow, map_natCast, scaledLift_spec]
  ring

theorem scaledLift_one : scaledLift p C j hj f hb 1 = (p : R) ^ C := by
  apply hj
  rw [scaledLift_spec, map_one, mul_one, map_pow, map_natCast]

def scaledLiftMod (n : ℕ) :
    A ⧸ (Ideal.span {(p : A)}) ^ n →+ R ⧸ (Ideal.span {(p : R)}) ^ n :=
  QuotientAddGroup.lift ((Ideal.span {(p : A)}) ^ n).toAddSubgroup
    ((Ideal.Quotient.mk _).toAddMonoidHom.comp (scaledLift p C j hj f hb)) (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change a ∈ (Ideal.span {(p : A)}) ^ n at ha
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha ⊢
      obtain ⟨b, rfl⟩ := ha
      refine ⟨scaledLift p C j hj f hb b, ?_⟩
      simpa only [Nat.cast_pow] using scaledLift_nat_mul p C j hj f hb (p ^ n) b)

theorem scaledLiftMod_mk (n : ℕ) (a : A) :
    scaledLiftMod p C j hj f hb n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (scaledLift p C j hj f hb a) := rfl

def scaledComponent (n : ℕ) : AdicCompletion (Ideal.span {(p : A)}) A →+
    R ⧸ (Ideal.span {(p : R)}) ^ n :=
  (scaledLiftMod p C j hj f hb n).comp
    (AdicCompletion.evalₐ (Ideal.span {(p : A)}) n).toRingHom.toAddMonoidHom

theorem scaledComponent_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : R)}) h).toAddMonoidHom.comp
      (scaledComponent p C j hj f hb n) = scaledComponent p C j hj f hb m := by
  apply AddMonoidHom.ext
  intro x
  apply AdicCompletion.induction_on (Ideal.span {(p : A)}) A x
  intro c
  change Ideal.Quotient.factorPow (Ideal.span {(p : R)}) h
    (scaledLiftMod p C j hj f hb n (AdicCompletion.evalₐ _ n (AdicCompletion.mk _ A c))) =
    scaledLiftMod p C j hj f hb m (AdicCompletion.evalₐ _ m (AdicCompletion.mk _ A c))
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk,
    scaledLiftMod_mk, scaledLiftMod_mk, Ideal.Quotient.factor_mk]
  apply Ideal.Quotient.eq.mpr
  have hc : c.val n - c.val m ∈ (Ideal.span {(p : A)}) ^ m := by
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using (c.property h).symm
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hc ⊢
  obtain ⟨b, hb'⟩ := hc
  refine ⟨scaledLift p C j hj f hb b, ?_⟩
  rw [← map_sub, hb']
  simpa only [Nat.cast_pow] using scaledLift_nat_mul p C j hj f hb (p ^ m) b

def scaledCompletion : AdicCompletion (Ideal.span {(p : A)}) A →+
    AdicCompletion (Ideal.span {(p : R)}) R :=
  adicLiftAddHom _ (scaledComponent p C j hj f hb)
    (fun h => scaledComponent_compatible p C j hj f hb h)

variable [IsAdicComplete (Ideal.span {(p : R)}) R]

def scaledExtension : AdicCompletion (Ideal.span {(p : A)}) A →+ R :=
  (AdicCompletion.ofAlgEquiv (Ideal.span {(p : R)})).symm.toRingEquiv.toAddMonoidHom.comp
    (scaledCompletion p C j hj f hb)

theorem mk_scaledExtension (n : ℕ) (x : AdicCompletion (Ideal.span {(p : A)}) A) :
    Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ n) (scaledExtension p C j hj f hb x) =
      scaledLiftMod p C j hj f hb n (AdicCompletion.evalₐ (Ideal.span {(p : A)}) n x) := by
  change Ideal.Quotient.mk _ ((AdicCompletion.ofAlgEquiv _).symm _) = _
  rw [AdicCompletion.mk_ofAlgEquiv_symm, scaledCompletion, eval_adicLiftAddHom]
  rfl

theorem scaledExtension_of (a : A) :
    scaledExtension p C j hj f hb (AdicCompletion.of (Ideal.span {(p : A)}) A a) =
      scaledLift p C j hj f hb a := by
  apply eq_of_quotient_eq (Ideal.span {(p : R)})
  intro n
  rw [mk_scaledExtension, AdicCompletion.evalₐ_of, scaledLiftMod_mk]

theorem scaledExtension_one : scaledExtension p C j hj f hb 1 = (p : R) ^ C := by
  have he := scaledExtension_of p C j hj f hb (1 : A)
  rw [scaledLift_one] at he
  exact he

theorem scaledExtension_mul (x y : AdicCompletion (Ideal.span {(p : A)}) A) :
    (p : R) ^ C * scaledExtension p C j hj f hb (x * y) =
      scaledExtension p C j hj f hb x * scaledExtension p C j hj f hb y := by
  apply eq_of_quotient_eq (Ideal.span {(p : R)})
  intro n
  simp only [map_mul, map_pow, map_natCast, mk_scaledExtension]
  generalize AdicCompletion.evalₐ (Ideal.span {(p : A)}) n x = a
  generalize AdicCompletion.evalₐ (Ideal.span {(p : A)}) n y = b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, scaledLiftMod_mk, scaledLiftMod_mk, scaledLiftMod_mk]
  simpa only [map_mul, map_pow, map_natCast] using
    congrArg (Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ n))
      (scaledLift_mul p C j hj f hb a b)

variable (hu : IsUnit (p : S))

def boundedExtension : AdicCompletion (Ideal.span {(p : A)}) A →+* S where
  toFun x := ↑((hu.pow C).unit⁻¹) * j (scaledExtension p C j hj f hb x)
  map_zero' := by rw [map_zero, map_zero, mul_zero]
  map_add' x y := by rw [map_add, map_add, mul_add]
  map_one' := by
    rw [scaledExtension_one, map_pow, map_natCast]
    exact (hu.pow C).val_inv_mul
  map_mul' x y := by
    have he := congrArg j (scaledExtension_mul p C j hj f hb x y)
    simp only [j.map_mul, j.map_pow, map_natCast] at he
    have hi := (hu.pow C).val_inv_mul
    have hi' : (p : S) ^ C * ↑((hu.pow C).unit⁻¹) = 1 := by simpa only [mul_comm] using hi
    apply (hu.pow C).mul_left_cancel
    calc
      (p : S) ^ C * (↑((hu.pow C).unit⁻¹) * j (scaledExtension p C j hj f hb (x * y))) =
          j (scaledExtension p C j hj f hb (x * y)) := by rw [← mul_assoc, hi', one_mul]
      _ = ↑((hu.pow C).unit⁻¹) *
          ((p : S) ^ C * j (scaledExtension p C j hj f hb (x * y))) := by
            rw [← mul_assoc, hi, one_mul]
      _ = ↑((hu.pow C).unit⁻¹) *
          (j (scaledExtension p C j hj f hb x) * j (scaledExtension p C j hj f hb y)) := by rw [he]
      _ = (p : S) ^ C * ((↑((hu.pow C).unit⁻¹) * j (scaledExtension p C j hj f hb x)) *
          (↑((hu.pow C).unit⁻¹) * j (scaledExtension p C j hj f hb y))) := by
        calc
          _ = ((p : S) ^ C * ↑((hu.pow C).unit⁻¹)) *
              (↑((hu.pow C).unit⁻¹) * (j (scaledExtension p C j hj f hb x) *
                j (scaledExtension p C j hj f hb y))) := by rw [hi', one_mul]
          _ = _ := by ring

theorem boundedExtension_scaled (x : AdicCompletion (Ideal.span {(p : A)}) A) :
    (p : S) ^ C * boundedExtension p C j hj f hb hu x = j (scaledExtension p C j hj f hb x) := by
  change (p : S) ^ C * (↑((hu.pow C).unit⁻¹) * _) = _
  rw [← mul_assoc, mul_comm ((p : S) ^ C), (hu.pow C).val_inv_mul, one_mul]

theorem boundedExtension_of (a : A) :
    boundedExtension p C j hj f hb hu (AdicCompletion.of (Ideal.span {(p : A)}) A a) = f a := by
  apply (hu.pow C).mul_left_cancel
  rw [boundedExtension_scaled, scaledExtension_of, scaledLift_spec]

theorem boundedExtension_bound (x : AdicCompletion (Ideal.span {(p : A)}) A) :
    ∃ r : R, j r = (p : S) ^ C * boundedExtension p C j hj f hb hu x :=
  ⟨scaledExtension p C j hj f hb x, (boundedExtension_scaled p C j hj f hb hu x).symm⟩

theorem boundedExtension_mk_of_stable
    (c : AdicCompletion.AdicCauchySequence (Ideal.span {(p : A)}) A)
    (s : S) (k : ℕ) (hc : ∀ n ≥ k, f (c.val n) = s) :
    boundedExtension p C j hj f hb hu (AdicCompletion.mk _ A c) = s := by
  have he : scaledExtension p C j hj f hb (AdicCompletion.mk _ A c) =
      scaledLift p C j hj f hb (c.val k) := by
    apply eq_of_quotient_eq (Ideal.span {(p : R)})
    intro n
    have hnk : scaledLift p C j hj f hb (c.val (n + k)) =
        scaledLift p C j hj f hb (c.val k) := by
      apply hj
      rw [scaledLift_spec, scaledLift_spec, hc (n + k) (Nat.le_add_left _ _), hc k le_rfl]
    have hm := mk_scaledExtension p C j hj f hb (n + k) (AdicCompletion.mk _ A c)
    rw [AdicCompletion.evalₐ_mk, scaledLiftMod_mk, hnk] at hm
    have ht := congrArg (Ideal.Quotient.factorPow (Ideal.span {(p : R)})
      (Nat.le_add_right n k)) hm
    simpa only [Ideal.Quotient.factor_mk] using ht
  apply (hu.pow C).mul_left_cancel
  rw [boundedExtension_scaled, he, scaledLift_spec, hc k le_rfl]

end ScaledMap

variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] (p : ℕ)

theorem exists_remainder (x : AdicCompletion (Ideal.span {(p : A)}) A) (n : ℕ) :
    ∃ a : A, ∃ z : AdicCompletion (Ideal.span {(p : A)}) A,
      x = AdicCompletion.of (Ideal.span {(p : A)}) A a + (p : AdicCompletion _ A) ^ n * z := by
  let I : Ideal A := Ideal.span {(p : A)}
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have he : AdicCompletion.evalₐ I n (x - AdicCompletion.of I A a) = 0 := by
    rw [map_sub, AdicCompletion.evalₐ_of, ha, sub_self]
  have hmem : x - AdicCompletion.of I A a ∈
      I ^ n • (⊤ : Submodule A (AdicCompletion I A)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker]
    rw [← AdicCompletion.factor_evalₐ_eq_eval I _ (by simp), he, map_zero]
  change x - AdicCompletion.of I A a ∈
    (Ideal.span {(p : A)}) ^ n • (⊤ : Submodule A (AdicCompletion I A)) at hmem
  rw [Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨z, _, hz⟩ := hmem
  have hz' : (p : AdicCompletion I A) ^ n * z = x - AdicCompletion.of I A a := by
    simpa only [Algebra.smul_def, map_pow, map_natCast] using hz
  exact ⟨a, z, by rw [hz']; ring⟩

variable (j : R →+* S) (hj : Function.Injective j)
theorem bound_mono {C D : ℕ} (hCD : C ≤ D) (s : S)
    (hs : ∃ r : R, j r = (p : S) ^ C * s) : ∃ r : R, j r = (p : S) ^ D * s := by
  obtain ⟨r, hr⟩ := hs
  refine ⟨(p : R) ^ (D - C) * r, ?_⟩
  rw [map_mul, map_pow, map_natCast, hr, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hCD]

variable [IsAdicComplete (Ideal.span {(p : R)}) R]

include hj in
theorem bounded_hom_unique (C : ℕ) (hu : IsUnit (p : S))
    (F G : AdicCompletion (Ideal.span {(p : A)}) A →+* S)
    (hagree : ∀ a : A, F (AdicCompletion.of _ A a) = G (AdicCompletion.of _ A a))
    (hF : ∀ x, ∃ r : R, j r = (p : S) ^ C * F x)
    (hG : ∀ x, ∃ r : R, j r = (p : S) ^ C * G x) : F = G := by
  apply RingHom.ext
  intro x
  obtain ⟨r, hr⟩ := hF x
  obtain ⟨s, hs⟩ := hG x
  have hrs : r = s := by
    apply eq_of_quotient_eq (Ideal.span {(p : R)})
    intro n
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨a, z, hx⟩ := exists_remainder p x n
    obtain ⟨b, hb⟩ := hF z
    obtain ⟨c, hc⟩ := hG z
    refine ⟨b - c, ?_⟩
    apply hj
    simp only [j.map_sub, j.map_mul, j.map_pow, map_natCast, hr, hs, hb, hc]
    rw [hx, F.map_add, G.map_add, F.map_mul, G.map_mul, F.map_pow, G.map_pow,
      map_natCast, map_natCast, hagree]
    ring
  apply (hu.pow C).mul_left_cancel
  rw [← hr, ← hs, hrs]

end NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion

namespace NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion.ModuleComparison

/-! Uniqueness of bounded additive comparison maps on completed modules. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion
variable {A M R S : Type*} [CommRing A] [AddCommGroup M] [Module A M] [CommRing R] [CommRing S]
variable (p : ℕ)

theorem module_remainder (x : AdicCompletion (Ideal.span {(p : A)}) M) (n : ℕ) :
    ∃ a : M, ∃ z : AdicCompletion (Ideal.span {(p : A)}) M,
      x = AdicCompletion.of (Ideal.span {(p : A)}) M a + (p : A) ^ n • z := by
  let I := Ideal.span {(p : A)}
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective _ (AdicCompletion.eval I M n x)
  have hm : x - AdicCompletion.of I M a ∈ I ^ n • (⊤ : Submodule A (AdicCompletion I M)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker]
    rw [map_sub, AdicCompletion.eval_of, ha, sub_self]
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hm
  obtain ⟨z, _, hz⟩ := hm
  exact ⟨a, z, by rw [hz]; abel⟩

theorem addHom_p_power_smul (F : M →+ S) (n : ℕ) (x : M) :
    F ((p : A) ^ n • x) = (p : S) ^ n * F x := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul, Nat.cast_pow]

variable (j : R →+* S) (hj : Function.Injective j)
variable [IsAdicComplete (Ideal.span {(p : R)}) R]

include hj in
theorem bounded_addHom_unique (C : ℕ) (hu : IsUnit (p : S))
    (F G : AdicCompletion (Ideal.span {(p : A)}) M →+ S)
    (hagree : ∀ a : M, F (AdicCompletion.of (Ideal.span {(p : A)}) M a) =
      G (AdicCompletion.of (Ideal.span {(p : A)}) M a))
    (hF : ∀ x, ∃ r : R, j r = (p : S) ^ C * F x)
    (hG : ∀ x, ∃ r : R, j r = (p : S) ^ C * G x) : F = G := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨r, hr⟩ := hF x
  obtain ⟨s, hs⟩ := hG x
  have hrs : r = s := by
    apply eq_of_quotient_eq (Ideal.span {(p : R)})
    intro n
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨a, z, hx⟩ := module_remainder p x n
    obtain ⟨b, hb⟩ := hF z
    obtain ⟨c, hc⟩ := hG z
    refine ⟨b - c, ?_⟩
    apply hj
    simp only [map_sub, map_mul, map_pow, map_natCast, hr, hs, hb, hc]
    rw [hx, F.map_add, G.map_add, addHom_p_power_smul, addHom_p_power_smul, hagree]
    ring
  apply (hu.pow C).mul_left_cancel
  rw [← hr, ← hs, hrs]

end NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion.ModuleComparison

end

end OAI
