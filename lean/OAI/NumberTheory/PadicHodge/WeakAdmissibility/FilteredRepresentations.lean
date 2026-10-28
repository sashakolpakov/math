import Mathlib

/-! # Filtered Representations -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.FilteredRepresentations.Construction

noncomputable section

/-!
Foundations for WeakAdmissibility, with the convention tH ≤ tN on subobjects.

This module defines the finite filtrations and filtered Frobenius modules used
by the native period-ring construction. The unconditional comparison and weak
admissibility theorem is proved in NativeWeakAdmissibility and exported by
Statements/WeakAdmissibility. No proof module imports the statement.
-/

universe u v

/-- A continuous p-adic representation of G_K in finite coordinates.
The absolute Galois group carries its Krull topology; continuity refers
to the joint action, not merely continuity of individual linear maps. -/
structure FinitePadicGaloisRep (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] where
  dimension : ℕ
  rho : Representation ℚ_[p] (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (Fin dimension → ℚ_[p])
  continuous_action : Continuous
    (fun x : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) × (Fin dimension → ℚ_[p]) =>
      rho x.1 x.2)

/-- A bounded decreasing filtration on a vector space. -/
structure FiniteFiltration (K : Type u) (D : Type v)
    [Field K] [AddCommGroup D] [Module K D] where
  step : ℤ → Submodule K D
  antitone_step : Antitone step
  eventually_top : ∃ a, step a = ⊤
  eventually_bot : ∃ b, step b = ⊥

namespace FiniteFiltration

variable {K : Type u} {D : Type v}
  [Field K] [AddCommGroup D] [Module K D]

theorem step_eq_top (F : FiniteFiltration K D) {a i : ℤ}
    (ha : F.step a = ⊤) (hi : i ≤ a) : F.step i = ⊤ := by
  apply top_unique
  simpa only [ha] using F.antitone_step hi

theorem step_eq_bot (F : FiniteFiltration K D) {b i : ℤ}
    (hb : F.step b = ⊥) (hi : b ≤ i) : F.step i = ⊥ := by
  apply bot_unique
  simpa only [hb] using F.antitone_step hi

/-- The filtration with its only jump at an arbitrary integer weight. -/
def pure (weight : ℤ) : FiniteFiltration K D where
  step i := if i ≤ weight then ⊤ else ⊥
  antitone_step := by
    intro i j hij
    dsimp only
    split_ifs with hj hi hi
    · exact le_rfl
    · omega
    · exact bot_le
    · exact le_rfl
  eventually_top := ⟨weight, by simp⟩
  eventually_bot := ⟨weight + 1, by simp⟩

/-- The induced filtration on a subspace. -/
def restrict (F : FiniteFiltration K D) (S : Submodule K D) :
    FiniteFiltration K S where
  step i := (F.step i).comap S.subtype
  antitone_step _ _ hij := Submodule.comap_mono (F.antitone_step hij)
  eventually_top := by
    obtain ⟨a, ha⟩ := F.eventually_top
    exact ⟨a, by simp [ha]⟩
  eventually_bot := by
    obtain ⟨b, hb⟩ := F.eventually_bot
    exact ⟨b, by simp [hb]⟩

/-- The quotient filtration, without an arbitrary choice of splitting. -/
def quotient (F : FiniteFiltration K D) (S : Submodule K D) :
    FiniteFiltration K (D ⧸ S) where
  step i := (F.step i).map S.mkQ
  antitone_step _ _ hij := Submodule.map_mono (F.antitone_step hij)
  eventually_top := by
    obtain ⟨a, ha⟩ := F.eventually_top
    exact ⟨a, by simp [ha]⟩
  eventually_bot := by
    obtain ⟨b, hb⟩ := F.eventually_bot
    exact ⟨b, by simp [hb]⟩

/-- The actual associated graded vector space in degree i. -/
abbrev Graded (F : FiniteFiltration K D) (i : ℤ) :=
  F.step i ⧸ (F.step (i + 1)).comap (F.step i).subtype

variable [FiniteDimensional K D]

theorem graded_finrank_add (F : FiniteFiltration K D) (i : ℤ) :
    Module.finrank K (F.Graded i) + Module.finrank K (F.step (i + 1)) =
      Module.finrank K (F.step i) := by
  have h := ((F.step (i + 1)).comap (F.step i).subtype).finrank_quotient_add_finrank
  have he := (Submodule.comapSubtypeEquivOfLe
    (F.antitone_step (show i ≤ i + 1 by omega))).finrank_eq
  simpa only [he] using h

theorem graded_finrank_eq_sub (F : FiniteFiltration K D) (i : ℤ) :
    Module.finrank K (F.Graded i) =
      Module.finrank K (F.step i) - Module.finrank K (F.step (i + 1)) := by
  have h := F.graded_finrank_add i
  omega

theorem graded_finrank_eq_zero_of_lt (F : FiniteFiltration K D) {a i : ℤ}
    (ha : F.step a = ⊤) (hi : i < a) :
    Module.finrank K (F.Graded i) = 0 := by
  rw [F.graded_finrank_eq_sub, F.step_eq_top ha (by omega),
    F.step_eq_top ha (by omega), Nat.sub_self]

theorem graded_finrank_eq_zero_of_le (F : FiniteFiltration K D) {b i : ℤ}
    (hb : F.step b = ⊥) (hi : b ≤ i) :
    Module.finrank K (F.Graded i) = 0 := by
  rw [F.graded_finrank_eq_sub, F.step_eq_bot hb hi,
    F.step_eq_bot hb (by omega), Nat.sub_self]

theorem graded_finrank_pure (weight i : ℤ) :
    Module.finrank K ((pure (K := K) (D := D) weight).Graded i) =
      if i = weight then Module.finrank K D else 0 := by
  by_cases hi : i = weight
  · subst i
    have htop : (pure (K := K) (D := D) weight).step weight = ⊤ := ite_eq_left le_rfl
    have hbot : (pure (K := K) (D := D) weight).step (weight + 1) = ⊥ :=
      ite_eq_right (by omega)
    rw [FiniteFiltration.graded_finrank_eq_sub, htop, hbot]
    simp
  · rw [ite_eq_right hi]
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · exact (pure (K := K) (D := D) weight).graded_finrank_eq_zero_of_lt
        (a := weight) (ite_eq_left le_rfl) hlt
    · exact (pure (K := K) (D := D) weight).graded_finrank_eq_zero_of_le
        (b := weight + 1) (ite_eq_right (by omega)) (by omega)

theorem graded_finrank_finite_support (F : FiniteFiltration K D) :
    (Function.support (fun i : ℤ => Module.finrank K (F.Graded i))).Finite := by
  obtain ⟨a, ha⟩ := F.eventually_top
  obtain ⟨b, hb⟩ := F.eventually_bot
  apply (Set.finite_Ico a b).subset
  intro i hi
  have hne : Module.finrank K (F.Graded i) ≠ 0 := hi
  constructor
  · by_contra h
    exact hne (F.graded_finrank_eq_zero_of_lt ha (by omega))
  · by_contra h
    exact hne (F.graded_finrank_eq_zero_of_le hb (by omega))

/-- Hodge number from the dimensions of the actual associated graded pieces. -/
def tH (F : FiniteFiltration K D) : ℚ :=
  ∑ᶠ i : ℤ, (i : ℚ) * Module.finrank K (F.Graded i)

theorem hodge_summand_finite_support (F : FiniteFiltration K D) :
    (Function.support (fun i : ℤ =>
      (i : ℚ) * Module.finrank K (F.Graded i))).Finite := by
  apply F.graded_finrank_finite_support.subset
  intro i hi hz
  apply hi
  simp [hz]

/-- In particular, weight -1 in dimension one has Hodge number -1. -/
theorem tH_pure (weight : ℤ) :
    (pure (K := K) (D := D) weight).tH = (weight : ℚ) * Module.finrank K D := by
  unfold FiniteFiltration.tH
  rw [finsum_eq_single _ weight (by
    intro i hi
    simp [graded_finrank_pure, hi])]
  rw [graded_finrank_pure, ite_eq_left rfl]

/-- Rank-nullity on every filtration step, using induced and quotient filtrations. -/
theorem step_finrank_add (F : FiniteFiltration K D) (S : Submodule K D) (i : ℤ) :
    Module.finrank K ((F.restrict S).step i) +
      Module.finrank K ((F.quotient S).step i) = Module.finrank K (F.step i) := by
  let f := S.mkQ.domRestrict (F.step i)
  let e : LinearMap.ker f ≃ₗ[K] (F.restrict S).step i :=
    { toFun := fun x => ⟨⟨x.1.1, (Submodule.Quotient.mk_eq_zero S).mp x.2⟩, x.1.2⟩
      invFun := fun x => ⟨⟨x.1.1, x.2⟩, (Submodule.Quotient.mk_eq_zero S).mpr x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := f.finrank_range_add_finrank_ker
  rw [e.finrank_eq] at h
  change Module.finrank K (LinearMap.range (S.mkQ.domRestrict (F.step i))) +
    Module.finrank K ((F.restrict S).step i) = Module.finrank K (F.step i) at h
  rw [LinearMap.range_domRestrict] at h
  exact (add_comm _ _).trans h

/-- The dimensions of associated graded pieces are additive. -/
theorem graded_finrank_add_sub_quotient (F : FiniteFiltration K D)
    (S : Submodule K D) (i : ℤ) :
    Module.finrank K ((F.restrict S).Graded i) +
      Module.finrank K ((F.quotient S).Graded i) = Module.finrank K (F.Graded i) := by
  have h₀ := F.step_finrank_add S i
  have h₁ := F.step_finrank_add S (i + 1)
  have h₂ := (F.restrict S).graded_finrank_add i
  have h₃ := (F.quotient S).graded_finrank_add i
  have h₄ := F.graded_finrank_add i
  omega

/-- Hodge numbers are additive for a subspace with its induced filtration. -/
theorem tH_add_sub_quotient (F : FiniteFiltration K D) (S : Submodule K D) :
    (F.restrict S).tH + (F.quotient S).tH = F.tH := by
  unfold FiniteFiltration.tH
  rw [← finsum_add_distrib (F.restrict S).hodge_summand_finite_support
    (F.quotient S).hodge_summand_finite_support]
  congr 1
  funext i
  rw [← mul_add, ← Nat.cast_add, F.graded_finrank_add_sub_quotient S i]

end FiniteFiltration

/-- Valuation of a determinant, divided by the Frobenius period. -/
def normalizedDeterminant {K D : Type*} [Field K] [AddCommGroup D]
    [Module K D] (ν : AddValuation K (WithTop ℚ)) (f : ℕ) (T : D →ₗ[K] D) : ℚ :=
  (ν T.det).untop₀ / f

/-- Newton-number additivity is a consequence of the determinant factorization. -/
theorem normalizedDeterminant_add {K D : Type*} [Field K] [AddCommGroup D]
    [Module K D] [FiniteDimensional K D]
    (ν : AddValuation K (WithTop ℚ)) (f : ℕ)
    (T : D →ₗ[K] D) (hT : T.det ≠ 0)
    (S : Submodule K D) (hS : S ≤ S.comap T) :
    normalizedDeterminant ν f T =
      normalizedDeterminant ν f (T.restrict hS) +
      normalizedDeterminant ν f (S.mapQ S T hS) := by
  have hprod : (T.restrict hS).det * (S.mapQ S T hS).det ≠ 0 := by
    rw [← LinearMap.det_eq_det_mul_det S T hS]
    exact hT
  have h₁ := ν.ne_top_iff.mpr (mul_ne_zero_iff.mp hprod).1
  have h₂ := ν.ne_top_iff.mpr (mul_ne_zero_iff.mp hprod).2
  unfold normalizedDeterminant
  rw [LinearMap.det_eq_det_mul_det S T hS, ν.map_mul,
    WithTop.untop₀_add h₁ h₂, add_div]

/-- Semilinear Frobenius over a base with a specified positive Frobenius period.
The period is [K₀: ℚ_p] in the intended application. -/
structure PeriodicFrobenius (K : Type u) (D : Type v)
    [Field K] [AddCommGroup D] [Module K D] where
  sigma : K ≃+* K
  phi : D ≃+ D
  semilinear : ∀ (a : K) (x : D), phi (a • x) = sigma a • phi x
  period : ℕ
  period_pos : 0 < period
  sigma_period : ∀ a : K, (sigma : K → K)^[period] a = a

namespace PeriodicFrobenius

variable {K : Type u} {D : Type v}
  [Field K] [AddCommGroup D] [Module K D]

theorem iterate_add (P : PeriodicFrobenius K D) (n : ℕ) (x y : D) :
    (P.phi : D → D)^[n] (x + y) =
      (P.phi : D → D)^[n] x + (P.phi : D → D)^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

theorem iterate_smul (P : PeriodicFrobenius K D) (n : ℕ) (a : K) (x : D) :
    (P.phi : D → D)^[n] (a • x) =
      (P.sigma : K → K)^[n] a • (P.phi : D → D)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, P.semilinear]

/-- The iterate φ^f is K-linear. -/
def linearIterate (P : PeriodicFrobenius K D) : D →ₗ[K] D where
  toFun := (P.phi : D → D)^[P.period]
  map_add' := P.iterate_add P.period
  map_smul' a x := by
    change (P.phi : D → D)^[P.period] (a • x) =
      a • (P.phi : D → D)^[P.period] x
    rw [P.iterate_smul, P.sigma_period]

theorem linearIterate_bijective (P : PeriodicFrobenius K D) :
    Function.Bijective P.linearIterate := P.phi.bijective.iterate P.period

/-- The linear Frobenius iterate is an automorphism. -/
def linearIterateEquiv (P : PeriodicFrobenius K D) : D ≃ₗ[K] D :=
  LinearEquiv.ofBijective P.linearIterate P.linearIterate_bijective

@[simp]
theorem linearIterateEquiv_toLinearMap (P : PeriodicFrobenius K D) :
    P.linearIterateEquiv.toLinearMap = P.linearIterate := by
  ext x
  exact LinearEquiv.ofBijective_apply _ x

/-- Stability is only a condition on the subspace, with no numerical hypothesis. -/
def Stable (P : PeriodicFrobenius K D) (S : Submodule K D) : Prop :=
  ∀ x ∈ S, P.phi x ∈ S

theorem iterate_mem (P : PeriodicFrobenius K D) (S : Submodule K D)
    (hS : P.Stable S) (n : ℕ) {x : D} (hx : x ∈ S) :
    (P.phi : D → D)^[n] x ∈ S := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hS _ ih

theorem linearIterate_stable (P : PeriodicFrobenius K D) (S : Submodule K D)
    (hS : P.Stable S) : S ≤ S.comap P.linearIterate := by
  intro x hx
  exact P.iterate_mem S hS P.period hx

variable [FiniteDimensional K D]

/-- On a stable subspace the linear iterate is again invertible. -/
def restrictLinearIterateEquiv (P : PeriodicFrobenius K D) (S : Submodule K D)
    (hS : P.Stable S) : S ≃ₗ[K] S := by
  let f := P.linearIterate.restrict (P.linearIterate_stable S hS)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply P.linearIterate_bijective.1
    exact congrArg Subtype.val hxy
  exact LinearEquiv.ofBijective f ⟨hf, LinearMap.injective_iff_surjective.mp hf⟩

@[simp]
theorem restrictLinearIterateEquiv_toLinearMap (P : PeriodicFrobenius K D)
    (S : Submodule K D) (hS : P.Stable S) :
    (P.restrictLinearIterateEquiv S hS).toLinearMap =
      P.linearIterate.restrict (P.linearIterate_stable S hS) := by
  ext x
  rfl

/-- Normalized Newton number from the determinant of the actual linear iterate.
The valuation must be normalized by v_p(p)=1 in the application to WeakAdmissibility. -/
def tN (P : PeriodicFrobenius K D) (ν : AddValuation K (WithTop ℚ)) : ℚ :=
  (ν (LinearEquiv.det P.linearIterateEquiv : K)).untop₀ / P.period

def subobjectTN (P : PeriodicFrobenius K D) (ν : AddValuation K (WithTop ℚ))
    (S : Submodule K D) (hS : P.Stable S) : ℚ :=
  (ν (LinearEquiv.det (P.restrictLinearIterateEquiv S hS) : K)).untop₀ / P.period

omit [FiniteDimensional K D] in
/-- The determinant valuation used for tN is finite. -/
theorem determinant_valuation_ne_top (P : PeriodicFrobenius K D)
    (ν : AddValuation K (WithTop ℚ)) :
    ν (LinearEquiv.det P.linearIterateEquiv : K) ≠ ⊤ :=
  ν.ne_top_iff.mpr (Units.ne_zero _)

theorem subobject_determinant_valuation_ne_top (P : PeriodicFrobenius K D)
    (ν : AddValuation K (WithTop ℚ)) (S : Submodule K D) (hS : P.Stable S) :
    ν (LinearEquiv.det (P.restrictLinearIterateEquiv S hS) : K) ≠ ⊤ :=
  ν.ne_top_iff.mpr (Units.ne_zero _)

def quotientTN (P : PeriodicFrobenius K D) (ν : AddValuation K (WithTop ℚ))
    (S : Submodule K D) (hS : P.Stable S) : ℚ :=
  normalizedDeterminant ν P.period
    (S.mapQ S P.linearIterate (P.linearIterate_stable S hS))

theorem tN_add_sub_quotient (P : PeriodicFrobenius K D)
    (ν : AddValuation K (WithTop ℚ)) (S : Submodule K D) (hS : P.Stable S) :
    P.tN ν = P.subobjectTN ν S hS + P.quotientTN ν S hS := by
  have hT : P.linearIterate.det ≠ 0 := by
    simpa only [LinearEquiv.coe_det, LinearEquiv.coe_coe, linearIterateEquiv_toLinearMap] using
      Units.ne_zero (LinearEquiv.det P.linearIterateEquiv)
  simpa only [PeriodicFrobenius.tN, PeriodicFrobenius.subobjectTN, PeriodicFrobenius.quotientTN, normalizedDeterminant,
    LinearEquiv.coe_det, LinearEquiv.coe_coe, linearIterateEquiv_toLinearMap,
    restrictLinearIterateEquiv_toLinearMap] using
    normalizedDeterminant_add ν P.period P.linearIterate hT S
    (P.linearIterate_stable S hS)

end PeriodicFrobenius

open scoped TensorProduct

/-- Algebraic data of a filtered Frobenius module over K/K₀.
No admissibility assertion is part of this structure. -/
structure FilteredFrobeniusModule
    (K₀ K D : Type*) [Field K₀] [Field K] [Algebra K₀ K]
    [AddCommGroup D] [Module K₀ D] where
  frobenius : PeriodicFrobenius K₀ D
  filtration : FiniteFiltration K (K ⊗[K₀] D)

namespace FilteredFrobeniusModule

variable {K₀ K D : Type*} [Field K₀] [Field K] [Algebra K₀ K]
  [AddCommGroup D] [Module K₀ D] [FiniteDimensional K₀ D]

/-- Hodge number after the required extension of scalars to K. -/
def tH (M : FilteredFrobeniusModule K₀ K D) : ℚ := M.filtration.tH

/-- Hodge number of the induced filtration on the scalar extension of S. -/
def subobjectTH (M : FilteredFrobeniusModule K₀ K D) (S : Submodule K₀ D) : ℚ :=
  (M.filtration.restrict (S.baseChange K)).tH

/-- The numerical target of WeakAdmissibility, independently defined from crystalline
representations. The inequality uses every Frobenius-stable K₀-subspace. -/
def WeaklyAdmissible (M : FilteredFrobeniusModule K₀ K D)
    (ν : AddValuation K₀ (WithTop ℚ)) : Prop :=
  M.tH = M.frobenius.tN ν ∧
    ∀ (S : Submodule K₀ D) (hS : M.frobenius.Stable S),
      M.subobjectTH S ≤ M.frobenius.subobjectTN ν S hS

end FilteredFrobeniusModule

section PeriodEigenvectors

variable {B : Type*} [CommRing B]

/-- Dividing a Frobenius eigenvector by a unit with the same multiplier
produces a fixed vector. This is an identity in the period ring. -/
theorem normalized_eigenvector_fixed
    (φ : B →+* B) (w : Bˣ) (b : B)
    (hb : φ b = φ (w : B) * (↑w⁻¹ : B) * b) :
    φ ((↑w⁻¹ : B) * b) = (↑w⁻¹ : B) * b := by
  rw [map_mul, hb]
  calc
    φ (↑w⁻¹ : B) * (φ (w : B) * (↑w⁻¹ : B) * b) =
        (φ (↑w⁻¹ : B) * φ (w : B)) * ((↑w⁻¹ : B) * b) := by ring
    _ = (↑w⁻¹ : B) * b := by rw [← map_mul]; simp

/-- The algebraic normalization step in the period-ring proof of the
Hodge-Newton inequality. Its fixed-vector hypothesis must still be proved
for the actual crystalline period ring before it can be applied to WeakAdmissibility. -/
theorem eigenvector_filtration_bound_of_fixed_vanishing
    (Fil : ℤ → AddSubgroup B) (hanti : Antitone Fil)
    (hmul : ∀ (i j : ℤ) (x y : B),
      x ∈ Fil i → y ∈ Fil j → x * y ∈ Fil (i + j))
    (φ : B →+* B)
    (hfixed : ∀ x : B, x ∈ Fil 1 → φ x = x → x = 0)
    (w : Bˣ) (n s : ℤ) (hw : (↑w⁻¹ : B) ∈ Fil (-n))
    (b : B) (hb : b ≠ 0) (hbs : b ∈ Fil s)
    (hφb : φ b = φ (w : B) * (↑w⁻¹ : B) * b) : s ≤ n := by
  by_contra h
  have hpos : 1 ≤ -n + s := by omega
  have hmem : (↑w⁻¹ : B) * b ∈ Fil 1 :=
    hanti hpos (hmul (-n) s _ _ hw hbs)
  have hz := hfixed _ hmem (normalized_eigenvector_fixed φ w b hφb)
  apply hb
  have hx := congrArg (fun x : B => (w : B) * x) hz
  simpa [← mul_assoc] using hx

end PeriodEigenvectors

/-- The proved Witt-vector Frobenius equation normalizes an arbitrary
nonzero coefficient eigenvalue to an integral power of p. -/
theorem normalize_coefficient_eigenvalue
    (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [IsAlgClosed k] [CharP k p]
    (B : Type*) [CommRing B]
    (j : FractionRing (WittVector p k) →+* B)
    (φ : B →+* B)
    (hφj : ∀ a : FractionRing (WittVector p k),
      φ (j a) = j (WittVector.FractionRing.frobenius p k a))
    (a : FractionRing (WittVector p k)) (ha : a ≠ 0)
    (x : B) (hx : φ x = j a * x) :
    ∃ c : FractionRing (WittVector p k), c ≠ 0 ∧
      ∃ n : ℤ, φ (j c * x) =
        j ((p : FractionRing (WittVector p k)) ^ n) * (j c * x) := by
  obtain ⟨c, hc, n, hn⟩ := WittVector.exists_frobenius_solution_fractionRing p ha
  refine ⟨c, hc, n, ?_⟩
  rw [map_mul, hφj, hx, ← mul_assoc, ← map_mul]
  change j (WittVector.FractionRing.frobenius p k c * a) * x = _
  rw [show WittVector.FractionRing.frobenius p k c * a =
    (p : FractionRing (WittVector p k)) ^ n * c from hn, map_mul, mul_assoc]

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.FilteredRepresentations.Construction
