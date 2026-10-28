import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuadraticCancellationEq

/-! # Quaternion Norm Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuaternionNormSymmetry.PositiveQuaternionNorm

noncomputable section

section

/-! Elementary norm identities for the positive rational quaternion
form with coefficients `1, 1, d, d`. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuadraticCancellationEq.QuadraticCancellation QuadraticMap

abbrev Vector := (ℚ × ℚ) × (ℚ × ℚ)

def two (c : ℚ) : QuadraticForm ℚ (ℚ × ℚ) := (QuadraticCancellationEq.QuadraticCancellation.scalar c).prod (QuadraticCancellationEq.QuadraticCancellation.scalar c)

def form (d : ℚ) : QuadraticForm ℚ Vector := (two 1).prod (two d)

@[simp] theorem two_apply (c : ℚ) (x : ℚ × ℚ) :
    two c x = c * (x.1 ^ 2 + x.2 ^ 2) := by
  simp only [two, prod_apply, QuadraticCancellationEq.QuadraticCancellation.scalar_apply]
  ring

@[simp] theorem form_apply (d : ℚ) (x : Vector) :
    form d x = x.1.1 ^ 2 + x.1.2 ^ 2 + d * (x.2.1 ^ 2 + x.2.2 ^ 2) := by
  simp [form]

def Represents (d a : ℚ) : Prop := ∃ x : Vector, form d x = a

theorem form_nonneg {d : ℚ} (hd : 0 < d) (x : Vector) : 0 ≤ form d x := by
  rw [form_apply]
  positivity

theorem form_eq_zero_iff {d : ℚ} (hd : 0 < d) (x : Vector) :
    form d x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    rw [form_apply] at hx
    have hu : 0 ≤ x.1.1 ^ 2 + x.1.2 ^ 2 := by positivity
    have hv : 0 ≤ x.2.1 ^ 2 + x.2.2 ^ 2 := by positivity
    have hv0 : x.2.1 ^ 2 + x.2.2 ^ 2 = 0 := by nlinarith
    have hu0 : x.1.1 ^ 2 + x.1.2 ^ 2 = 0 := by nlinarith
    have h0 : x.1.1 = 0 := by nlinarith [sq_nonneg x.1.2]
    have h1 : x.1.2 = 0 := by nlinarith [sq_nonneg x.1.1]
    have h2 : x.2.1 = 0 := by nlinarith [sq_nonneg x.2.2]
    have h3 : x.2.2 = 0 := by nlinarith [sq_nonneg x.2.1]
    exact Prod.ext (Prod.ext h0 h1) (Prod.ext h2 h3)
  · rintro rfl
    exact (form d).map_zero

def multiply (d : ℚ) (u v : Vector) : Vector :=
  ((u.1.1 * v.1.1 - u.1.2 * v.1.2 - d * u.2.1 * v.2.1 - d * u.2.2 * v.2.2,
    u.1.1 * v.1.2 + u.1.2 * v.1.1 + d * u.2.1 * v.2.2 - d * u.2.2 * v.2.1),
   (u.1.1 * v.2.1 - u.1.2 * v.2.2 + u.2.1 * v.1.1 + u.2.2 * v.1.2,
    u.1.1 * v.2.2 + u.1.2 * v.2.1 - u.2.1 * v.1.2 + u.2.2 * v.1.1))

theorem form_multiply (d : ℚ) (u v : Vector) :
    form d (multiply d u v) = form d u * form d v := by
  simp only [form_apply, multiply]
  ring

def multiplyLinear (d : ℚ) (u : Vector) : Vector →ₗ[ℚ] Vector where
  toFun := multiply d u
  map_add' x y := by
    ext <;> simp only [multiply, Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' a x := by
    ext <;> dsimp [multiply] <;> ring

theorem multiplyLinear_injective {d : ℚ} (hd : 0 < d) (u : Vector)
    (hu : form d u ≠ 0) : Function.Injective (multiplyLinear d u) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  apply (form_eq_zero_iff hd v).mp
  have h := form_multiply d u v
  change multiply d u v = 0 at hv
  rw [hv, (form d).map_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hu

theorem represents_one (d : ℚ) : Represents d 1 := by
  exact ⟨((1, 0), (0, 0)), by simp⟩

theorem represents_two (d : ℚ) : Represents d 2 := by
  exact ⟨((1, 1), (0, 0)), by norm_num⟩

theorem represents_self (d : ℚ) : Represents d d := by
  exact ⟨((0, 0), (1, 0)), by simp⟩

theorem Represents.mul {d a b : ℚ} (ha : Represents d a) (hb : Represents d b) :
    Represents d (a * b) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  exact ⟨multiply d u v, by rw [form_multiply, hu, hv]⟩

theorem Represents.inv {d a : ℚ} (ha : Represents d a) (ha0 : a ≠ 0) :
    Represents d a⁻¹ := by
  obtain ⟨u, hu⟩ := ha
  refine ⟨a⁻¹ • u, ?_⟩
  rw [(form d).map_smul, hu, smul_eq_mul]
  field_simp

theorem Represents.div {d a b : ℚ} (ha : Represents d a) (hb : Represents d b)
    (hb0 : b ≠ 0) : Represents d (a / b) := by
  simpa only [div_eq_mul_inv] using ha.mul (hb.inv hb0)

theorem rational_four_squares (a : ℚ) (ha : 0 < a) : Represents 1 a := by
  obtain ⟨w, x, y, z, h⟩ := Nat.sum_four_squares (a.num.natAbs * a.den)
  have hn : (a.num.natAbs : ℚ) = a.num := by
    have h := congrArg (fun n : ℤ => (n : ℚ))
      (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr ha.le))
    simpa only [Int.cast_natCast] using h
  have h' : (w : ℚ)^2 + (x : ℚ)^2 + (y : ℚ)^2 + (z : ℚ)^2 =
      (a.num : ℚ) * a.den := by
    have hc := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast at hc
    simpa only [hn] using hc
  have hd : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  refine ⟨(a.den : ℚ)⁻¹ • (((w : ℚ), (x : ℚ)), ((y : ℚ), (z : ℚ))), ?_⟩
  rw [(form 1).map_smul, smul_eq_mul, form_apply]
  simp only [one_mul]
  rw [← add_assoc, h']
  conv_rhs => rw [← a.num_div_den]
  field_simp

/-- The split norm comparison detects represented scalars. -/
def doubled (d a : ℚ) : QuadraticForm ℚ (Vector × Vector) :=
  (form d).prod ((-a) • form d)

theorem represents_iff_doubled_isotropic {d a : ℚ} (hd : 0 < d) :
    Represents d a ↔ ∃ x : Vector × Vector, x ≠ 0 ∧ doubled d a x = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨(u, ((1, 0), (0, 0))), ?_, ?_⟩
    · intro hz
      have h := congrArg (fun x : Vector × Vector => x.2.1.1) hz
      norm_num at h
    · simp [doubled, hu]
  · rintro ⟨⟨u, v⟩, hx, h⟩
    have hnorm : form d u = a * form d v := by
      simpa only [doubled, prod_apply, smul_apply, smul_eq_mul, neg_mul,
        ← sub_eq_add_neg, sub_eq_zero] using h
    have hv : form d v ≠ 0 := by
      intro hv
      have hv0 := (form_eq_zero_iff hd v).mp hv
      have hu0 := (form_eq_zero_iff hd u).mp (by rw [hnorm, hv, mul_zero])
      exact hx (Prod.ext hu0 hv0)
    have hr := (show Represents d (form d u) from ⟨u, rfl⟩).div
      (show Represents d (form d v) from ⟨v, rfl⟩) hv
    simpa only [hnorm, mul_div_cancel_right₀ _ hv] using hr

end

/-! Symmetry of positive rational quaternion norm representation. Four
equal positive squares are isometric after any positive rescaling, by
Lagrange's theorem and quaternion multiplication. Explicit hyperbolic
coordinate changes then reduce the comparison to quadratic cancellation. -/

open QuadraticMap OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuadraticCancellationEq.QuadraticCancellation

private def assoc {U V W : Type*}
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (Q : QuadraticForm ℚ U) (R : QuadraticForm ℚ V) (S : QuadraticForm ℚ W) :
    ((Q.prod R).prod S).IsometryEquiv (Q.prod (R.prod S)) where
  toLinearEquiv := LinearEquiv.prodAssoc ℚ U V W
  map_app' _ := (add_assoc _ _ _).symm

private theorem cancel_right {U V : Type*}
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (Q : QuadraticForm ℚ U) (R : QuadraticForm ℚ V) (c : ℚ) (hc : c ≠ 0)
    (h : (Q.prod (QuadraticCancellationEq.QuadraticCancellation.scalar c)).Equivalent (R.prod (QuadraticCancellationEq.QuadraticCancellation.scalar c))) : Q.Equivalent R := by
  apply QuadraticCancellationEq.QuadraticCancellation.cancel_scalar Q R c hc
  exact (show ((QuadraticCancellationEq.QuadraticCancellation.scalar c).prod Q).Equivalent (Q.prod (QuadraticCancellationEq.QuadraticCancellation.scalar c)) from
    ⟨IsometryEquiv.prodComm _ _⟩).trans
      (h.trans ⟨IsometryEquiv.prodComm _ _⟩)

private theorem cancel_two_right {U V : Type*}
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (Q : QuadraticForm ℚ U) (R : QuadraticForm ℚ V) (c : ℚ) (hc : c ≠ 0)
    (h : (Q.prod (two c)).Equivalent (R.prod (two c))) : Q.Equivalent R := by
  have h' : ((Q.prod (QuadraticCancellationEq.QuadraticCancellation.scalar c)).prod (QuadraticCancellationEq.QuadraticCancellation.scalar c)).Equivalent
      ((R.prod (QuadraticCancellationEq.QuadraticCancellation.scalar c)).prod (QuadraticCancellationEq.QuadraticCancellation.scalar c)) :=
    (show ((Q.prod (QuadraticCancellationEq.QuadraticCancellation.scalar c)).prod (QuadraticCancellationEq.QuadraticCancellation.scalar c)).Equivalent
      (Q.prod (two c)) from ⟨assoc Q (QuadraticCancellationEq.QuadraticCancellation.scalar c) (QuadraticCancellationEq.QuadraticCancellation.scalar c)⟩).trans
        (h.trans ⟨(assoc R (QuadraticCancellationEq.QuadraticCancellation.scalar c) (QuadraticCancellationEq.QuadraticCancellation.scalar c)).symm⟩)
  exact cancel_right Q R c hc (cancel_right _ _ c hc h')

private def four (c : ℚ) : QuadraticForm ℚ Vector := (two c).prod (two c)

private theorem four_apply (c : ℚ) (x : Vector) : four c x = c * form 1 x := by
  simp only [four, prod_apply, two_apply, form_apply, one_mul]
  ring

private theorem cancel_four_right {U V : Type*}
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (Q : QuadraticForm ℚ U) (R : QuadraticForm ℚ V) (c : ℚ) (hc : c ≠ 0)
    (h : (Q.prod (four c)).Equivalent (R.prod (four c))) : Q.Equivalent R := by
  have h' : ((Q.prod (two c)).prod (two c)).Equivalent
      ((R.prod (two c)).prod (two c)) :=
    (show ((Q.prod (two c)).prod (two c)).Equivalent
      (Q.prod (four c)) from ⟨assoc Q (two c) (two c)⟩).trans
        (h.trans ⟨(assoc R (two c) (two c)).symm⟩)
  exact cancel_two_right Q R c hc (cancel_two_right _ _ c hc h')

private theorem four_equivalent (c d : ℚ) (hc : 0 < c) (hd : 0 < d) :
    (four c).Equivalent (four d) := by
  obtain ⟨u, hu⟩ := rational_four_squares (c / d) (div_pos hc hd)
  have hu0 : form 1 u ≠ 0 := by rw [hu]; exact (div_pos hc hd).ne'
  let e := LinearEquiv.ofInjectiveEndo (multiplyLinear 1 u)
    (multiplyLinear_injective (by norm_num) u hu0)
  refine ⟨{ toLinearEquiv := e, map_app' := ?_ }⟩
  intro x
  change four d (multiply 1 u x) = four c x
  rw [four_apply, form_multiply, hu, four_apply]
  field_simp

private def hyperbolic (c : ℚ) : QuadraticForm ℚ Vector :=
  (two c).prod (two (-c))

private def hyperbolicMap (c d : ℚ) (x : Vector) : Vector :=
  ((((c / d + 1) / 2) * x.1.1 + ((c / d - 1) / 2) * x.2.1,
    ((c / d + 1) / 2) * x.1.2 + ((c / d - 1) / 2) * x.2.2),
   (((c / d - 1) / 2) * x.1.1 + ((c / d + 1) / 2) * x.2.1,
    ((c / d - 1) / 2) * x.1.2 + ((c / d + 1) / 2) * x.2.2))

private def hyperbolicEquiv (c d : ℚ) (hc : c ≠ 0) (hd : d ≠ 0) :
    (hyperbolic c).IsometryEquiv (hyperbolic d) where
  toFun := hyperbolicMap c d
  invFun := hyperbolicMap d c
  left_inv x := by
    ext <;> dsimp [hyperbolicMap] <;> field_simp [hc, hd] <;> ring
  right_inv x := by
    ext <;> dsimp [hyperbolicMap] <;> field_simp [hc, hd] <;> ring
  map_add' x y := by
    ext <;> dsimp [hyperbolicMap] <;> ring
  map_smul' a x := by
    ext <;> dsimp [hyperbolicMap] <;> ring
  map_app' x := by
    simp only [hyperbolic, prod_apply, two_apply, hyperbolicMap]
    field_simp [hd]
    ring

private def canonical (d a : ℚ) : QuadraticForm ℚ (Vector × Vector) :=
  ((two 1).prod (two d)).prod ((two (-a)).prod (two (-a * d)))

private def core (d a : ℚ) : QuadraticForm ℚ (Vector × Vector) :=
  ((two 1).prod (two d)).prod ((two a).prod (two (-a * d)))

private def doubledCanonical (d a : ℚ) :
    (doubled d a).IsometryEquiv (canonical d a) where
  toLinearEquiv := LinearEquiv.refl ℚ _
  map_app' x := by
    change canonical d a x = doubled d a x
    simp only [doubled, canonical, prod_apply, two_apply, form_apply, smul_apply,
      smul_eq_mul, one_mul]
    ring

private def exchangeLeft : ((Vector × Vector) × Vector) ≃ₗ[ℚ]
    ((Vector × Vector) × Vector) where
  toFun x := (((x.1.1.1, x.1.1.2), (x.2.1, x.1.2.2)), (x.1.2.1, x.2.2))
  invFun x := (((x.1.1.1, x.1.1.2), (x.2.1, x.1.2.2)), (x.1.2.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def exchangeRight : ((Vector × Vector) × Vector) ≃ₗ[ℚ]
    ((Vector × Vector) × Vector) where
  toFun x := (((x.1.1.1, x.2.1), (x.1.1.2, x.1.2.2)), (x.1.2.1, x.2.2))
  invFun x := (((x.1.1.1, x.1.2.1), (x.2.1, x.1.2.2)), (x.1.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def stableLeft (d a : ℚ) :
    ((canonical d a).prod (four a)).IsometryEquiv
      ((core d a).prod (hyperbolic (-a))) where
  toLinearEquiv := exchangeLeft
  map_app' x := by
    change (core d a).prod (hyperbolic (-a))
      (((x.1.1.1, x.1.1.2), (x.2.1, x.1.2.2)), (x.1.2.1, x.2.2)) = _
    simp only [canonical, core, four, hyperbolic, prod_apply, two_apply]
    ring

private def stableRight (d a : ℚ) :
    ((canonical a d).prod (four d)).IsometryEquiv
      ((core d a).prod (hyperbolic (-d))) where
  toLinearEquiv := exchangeRight
  map_app' x := by
    change (core d a).prod (hyperbolic (-d))
      (((x.1.1.1, x.2.1), (x.1.1.2, x.1.2.2)), (x.1.2.1, x.2.2)) = _
    simp only [canonical, core, four, hyperbolic, prod_apply, two_apply]
    ring

theorem doubled_equivalent_swap (d a : ℚ) (hd : 0 < d) (ha : 0 < a) :
    (doubled d a).Equivalent (doubled a d) := by
  have hstable : ((canonical d a).prod (four a)).Equivalent
      ((canonical a d).prod (four d)) :=
    ⟨(stableLeft d a).trans
      (((QuadraticMap.IsometryEquiv.refl (core d a)).prod
        (hyperbolicEquiv (-a) (-d) (neg_ne_zero.mpr ha.ne')
          (neg_ne_zero.mpr hd.ne'))).trans (stableRight d a).symm)⟩
  have hsame := hstable.trans
    ((Equivalent.refl (canonical a d)).prod (four_equivalent d a hd ha))
  have hc := cancel_four_right (canonical d a) (canonical a d) a ha.ne' hsame
  exact (show (doubled d a).Equivalent (canonical d a) from
    ⟨doubledCanonical d a⟩).trans (hc.trans ⟨(doubledCanonical a d).symm⟩)

theorem represents_swap {d a : ℚ} (hd : 0 < d) (ha : 0 < a) :
    Represents d a ↔ Represents a d := by
  obtain ⟨e⟩ := doubled_equivalent_swap d a hd ha
  rw [represents_iff_doubled_isotropic hd, represents_iff_doubled_isotropic ha]
  constructor
  · rintro ⟨x, hx, hq⟩
    exact ⟨e x, fun he => hx (e.injective (he.trans (map_zero e).symm)),
      (e.map_app x).trans hq⟩
  · rintro ⟨x, hx, hq⟩
    exact ⟨e.symm x, fun he => hx (e.symm.injective (he.trans (map_zero e.symm).symm)),
      (e.symm.map_app x).trans hq⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuaternionNormSymmetry.PositiveQuaternionNorm
