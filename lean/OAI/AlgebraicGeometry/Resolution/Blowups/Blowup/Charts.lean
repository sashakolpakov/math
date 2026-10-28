import OAI.AlgebraicGeometry.Resolution.Blowups.ReesGrading

/-! # Charts -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Charts.Construction

noncomputable section

/-! Affine chart maps for the Rees blowup used in Blowups. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The Rees-algebra element `a t` associated to an element of the ideal. -/
def reesGenerator (a : I) : reesAlgebra I :=
  ⟨monomial 1 a.val, reesAlgebra.monomial_mem.mpr (by simp)⟩

theorem reesGenerator_mem (a : I) : reesGenerator I a ∈ ReesGrading.Construction.reesGrade I 1 :=
  ReesGrading.Construction.monomial_mem_reesGrade I 1 a.val (by simp)

/-- Evaluation at `t = 1` on the actual Rees algebra. -/
def reesEvalOne : reesAlgebra I →+* R :=
  (Polynomial.evalRingHom 1).comp (reesAlgebra I).val.toRingHom

@[simp]
theorem reesEvalOne_generator (a : I) : reesEvalOne I (reesGenerator I a) = a := by
  simp [reesEvalOne, reesGenerator]

theorem reesEvalOne_homogeneous (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ ReesGrading.Construction.reesGrade I n) : reesEvalOne I p = p.val.coeff n := by
  change Polynomial.eval 1 p.val = _
  rw [ReesGrading.Construction.reesGrade_eq_monomial I n p hp]
  simp

theorem reesEvalOne_powers_le (a : I) :
    Submonoid.powers (reesGenerator I a) ≤ (Submonoid.powers a.val).comap (reesEvalOne I) := by
  rintro _ ⟨n, rfl⟩
  change reesEvalOne I ((reesGenerator I a) ^ n) ∈ Submonoid.powers a.val
  simp only [map_pow, reesEvalOne_generator]
  exact ⟨n, rfl⟩

/-- The affine chart `D₊(a t)` in the Rees projective spectrum. -/
abbrev blowupChart (a : I) :=
  HomogeneousLocalization.Away (ReesGrading.Construction.reesGrade I) (reesGenerator I a)

/-- The coefficient-fraction map from the chart to `R[1/a]`. -/
noncomputable def blowupChartToLocalization (a : I) :
    blowupChart I a →+* Localization.Away a.val :=
  (IsLocalization.map (Localization.Away a.val) (reesEvalOne I) (reesEvalOne_powers_le I a)).comp
    (algebraMap (blowupChart I a) (Localization.Away (reesGenerator I a)))

/-- A homogeneous fraction in the Rees chart maps to the corresponding
coefficient fraction in the localization of the base ring. -/
theorem blowupChartToLocalization_mk (a : I) (n : ℕ)
    (p : reesAlgebra I) (hp : p ∈ ReesGrading.Construction.reesGrade I (n • 1)) :
    blowupChartToLocalization I a
      (HomogeneousLocalization.Away.mk (ReesGrading.Construction.reesGrade I) (reesGenerator_mem I a) n p hp) =
      Localization.mk (p.val.coeff n) (⟨a.val ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers a.val) := by
  change IsLocalization.map (Localization.Away a.val) (reesEvalOne I)
    (reesEvalOne_powers_le I a)
    (Localization.mk p
      (⟨(reesGenerator I a) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (reesGenerator I a))) = _
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  · exact reesEvalOne_homogeneous I n p (by simpa using hp)
  · apply Subtype.ext
    simp

/-- The coefficient-fraction map identifies the chart with a subring of
`R[1/a]`; no domain assumption on `R` is needed. -/
theorem blowupChartToLocalization_injective (a : I) :
    Function.Injective (blowupChartToLocalization I a) := by
  intro x y hxy
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (ReesGrading.Construction.reesGrade I) (reesGenerator_mem I a) x
  obtain ⟨m, q, hq, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (ReesGrading.Construction.reesGrade I) (reesGenerator_mem I a) y
  rw [blowupChartToLocalization_mk, blowupChartToLocalization_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hxy
  obtain ⟨⟨_, ⟨k, rfl⟩⟩, hk⟩ := hxy
  change a.val ^ k * (a.val ^ m * p.val.coeff n) =
    a.val ^ k * (a.val ^ n * q.val.coeff m) at hk
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨(reesGenerator I a) ^ k, ⟨k, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change (monomial 1 a.val) ^ k * ((monomial 1 a.val) ^ m * p.val) =
    (monomial 1 a.val) ^ k * ((monomial 1 a.val) ^ n * q.val)
  rw [ReesGrading.Construction.reesGrade_eq_monomial I n p (by simpa using hp),
    ReesGrading.Construction.reesGrade_eq_monomial I m q (by simpa using hq)]
  simp only [monomial_pow, one_mul, monomial_mul_monomial]
  rw [Nat.add_comm m n, hk]

/-- The fraction `b / aⁿ` in the localization of the base ring. -/
def baseFraction (a : R) (n : ℕ) (b : R) : Localization.Away a :=
  Localization.mk b (⟨a ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers a)

@[simp]
theorem baseFraction_zero (a b : R) :
    baseFraction a 0 b = algebraMap R (Localization.Away a) b := by
  have hden : (⟨a ^ 0, ⟨0, rfl⟩⟩ : Submonoid.powers a) = 1 :=
    Subtype.ext (pow_zero a)
  unfold baseFraction
  rw [hden]
  rfl

theorem baseFraction_add (a : R) (n : ℕ) (b c : R) :
    baseFraction a n (b + c) = baseFraction a n b + baseFraction a n c :=
  (Localization.add_mk_self b _ c).symm

theorem baseFraction_mul (a : R) (n m : ℕ) (b c : R) :
    baseFraction a n b * baseFraction a m c = baseFraction a (n + m) (b * c) := by
  simp only [baseFraction, Localization.mk_mul]
  congr 1
  apply Subtype.ext
  exact (pow_add a n m).symm

/-- The fractions represented by an affine blowup chart are precisely those
whose degree-`n` numerator lies in the `n`th power of the center ideal. -/
theorem mem_range_blowupChartToLocalization_iff (a : I) (z : Localization.Away a.val) :
    z ∈ Set.range (blowupChartToLocalization I a) ↔
      ∃ (n : ℕ) (b : R), b ∈ I ^ n ∧ baseFraction a.val n b = z := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨n, p, hp, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (ReesGrading.Construction.reesGrade I) (reesGenerator_mem I a) x
    refine ⟨n, p.val.coeff n, p.property n, ?_⟩
    exact (blowupChartToLocalization_mk I a n p hp).symm
  · rintro ⟨n, b, hb, rfl⟩
    let p : reesAlgebra I := ⟨monomial n b, reesAlgebra.monomial_mem.mpr hb⟩
    have hp : p ∈ ReesGrading.Construction.reesGrade I (n • 1) := by
      simpa using ReesGrading.Construction.monomial_mem_reesGrade I n b hb
    refine ⟨HomogeneousLocalization.Away.mk (ReesGrading.Construction.reesGrade I) (reesGenerator_mem I a) n p hp, ?_⟩
    rw [blowupChartToLocalization_mk]
    simp [p, baseFraction]

/-- The chart, viewed as an actual subalgebra of the localized base ring. -/
def blowupChartImage (a : I) : Subalgebra R (Localization.Away a.val) where
  carrier := Set.range (blowupChartToLocalization I a)
  zero_mem' := ⟨0, map_zero _⟩
  one_mem' := ⟨1, map_one _⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ x y⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, map_mul _ x y⟩
  algebraMap_mem' r := by
    apply (mem_range_blowupChartToLocalization_iff I a _).mpr
    exact ⟨0, r, by simp, baseFraction_zero a.val r⟩

/-- The usual affine-chart description `R[I/a]` follows from the actual
homogeneous localization, including for base rings with zero divisors. -/
theorem blowupChartImage_eq_adjoin (a : I) :
    blowupChartImage I a =
      Algebra.adjoin R (Set.range (fun b : I => baseFraction a.val 1 b.val)) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨n, b, hb, rfl⟩ := (mem_range_blowupChartToLocalization_iff I a z).mp hz
    clear hz
    induction n generalizing b with
    | zero =>
      rw [baseFraction_zero]
      exact Subalgebra.algebraMap_mem _ b
    | succ n ih =>
      rw [pow_succ'] at hb
      refine Submodule.smul_induction_on hb ?_ ?_
      · intro r hr s hs
        change baseFraction a.val (n + 1) (r * s) ∈ _
        rw [Nat.add_comm n 1, ← baseFraction_mul]
        exact Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨⟨r, hr⟩, rfl⟩) (ih s hs)
      · intro r s hr hs
        rw [baseFraction_add]
        exact Subalgebra.add_mem _ hr hs
  · apply Algebra.adjoin_le
    rintro _ ⟨b, rfl⟩
    apply (mem_range_blowupChartToLocalization_iff I a _).mpr
    exact ⟨1, b.val, by simp, rfl⟩

/-- The elements `a t`, for `a ∈ I`, generate the Rees algebra over `R`. -/
theorem reesGenerators_adjoin :
    Algebra.adjoin R (Set.range (reesGenerator I)) = ⊤ := by
  apply Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  refine Eq.trans ?_ (adjoin_monomial_eq_reesAlgebra I)
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨a, rfl⟩, rfl⟩
    exact ⟨a.val, a.property, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨reesGenerator I ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩

/-- The same generators generate over the degree-zero coefficient ring. -/
theorem reesGenerators_adjoin_zero :
    Algebra.adjoin (ReesGrading.Construction.reesGrade I 0) (Set.range (reesGenerator I)) = ⊤ := by
  have hle : Algebra.adjoin R (Set.range (reesGenerator I)) ≤
      (Algebra.adjoin (ReesGrading.Construction.reesGrade I 0) (Set.range (reesGenerator I))).restrictScalars R :=
    Algebra.adjoin_le (fun _ hx => Algebra.subset_adjoin (R := ReesGrading.Construction.reesGrade I 0) hx)
  rw [reesGenerators_adjoin] at hle
  apply top_le_iff.mp
  intro p _
  exact hle (by trivial)

/-- The degree-one affine charts cover the actual affine blowup. -/
theorem affineBlowup_chart_cover :
    (⨆ a : I, Proj.basicOpen (ReesGrading.Construction.reesGrade I) (reesGenerator I a)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (ReesGrading.Construction.reesGrade I) (reesGenerator I)
    (fun a => ⟨1, reesGenerator_mem I a⟩) (reesGenerators_adjoin_zero I)

/-- The coefficient-ring morphism of a Rees blowup chart. -/
def blowupChartConstants (a : I) : R →+* blowupChart I a :=
  (HomogeneousLocalization.fromZeroRingHom (ReesGrading.Construction.reesGrade I)
    (Submonoid.powers (reesGenerator I a))).comp (algebraMap R (ReesGrading.Construction.reesGrade I 0))

@[simp]
theorem blowupChartToLocalization_constants (a : I) (r : R) :
    blowupChartToLocalization I a (blowupChartConstants I a r) =
      algebraMap R (Localization.Away a.val) r := by
  change IsLocalization.map (Localization.Away a.val) (reesEvalOne I)
    (reesEvalOne_powers_le I a)
    (Localization.mk (algebraMap R (reesAlgebra I) r)
      (1 : Submonoid.powers (reesGenerator I a))) = _
  rw [Localization.mk_one_eq_algebraMap, IsLocalization.map_eq]
  congr 1
  simp [reesEvalOne]

/-- A chart whose denominator is already a unit fills the whole localization. -/
theorem blowupChartToLocalization_surjective_of_isUnit (a : I) (ha : IsUnit a.val) :
    Function.Surjective (blowupChartToLocalization I a) := by
  intro z
  let e : R ≃ₐ[R] Localization.Away a.val :=
    IsLocalization.atUnit R (Localization.Away a.val) a.val ha
  obtain ⟨r, hr⟩ := e.surjective z
  have he : e r = algebraMap R (Localization.Away a.val) r := by
    simpa using e.commutes r
  change z ∈ Set.range (blowupChartToLocalization I a)
  apply (mem_range_blowupChartToLocalization_iff I a z).mpr
  exact ⟨0, r, by simp, (baseFraction_zero a.val r).trans (he.symm.trans hr)⟩

/-- When the denominator is a unit, the chart's coefficient map is bijective. -/
theorem blowupChartConstants_bijective_of_isUnit (a : I) (ha : IsUnit a.val) :
    Function.Bijective (blowupChartConstants I a) := by
  let e : R ≃ₐ[R] Localization.Away a.val :=
    IsLocalization.atUnit R (Localization.Away a.val) a.val ha
  have he (r : R) : e r = algebraMap R (Localization.Away a.val) r := by
    simpa using e.commutes r
  constructor
  · intro r s hrs
    apply e.injective
    rw [he, he, ← blowupChartToLocalization_constants, ← blowupChartToLocalization_constants, hrs]
  · intro x
    obtain ⟨r, hr⟩ := e.surjective (blowupChartToLocalization I a x)
    refine ⟨r, blowupChartToLocalization_injective I a ?_⟩
    rw [blowupChartToLocalization_constants, ← he, hr]

/-- A unit in the center ideal gives a degree-one element dividing every
other degree-one Rees generator. -/
theorem reesGenerator_dvd_of_isUnit (a : I) (ha : IsUnit a.val) (b : I) :
    reesGenerator I a ∣ reesGenerator I b := by
  obtain ⟨c, hc⟩ := (ha.dvd : a.val ∣ b.val)
  refine ⟨algebraMap R (reesAlgebra I) c, ?_⟩
  apply Subtype.ext
  change monomial 1 b.val = monomial 1 a.val * C c
  rw [monomial_mul_C, ← hc]

/-- The chart of a unit covers the whole Rees blowup. -/
theorem affineBlowup_unit_chart_eq_top (a : I) (ha : IsUnit a.val) :
    Proj.basicOpen (ReesGrading.Construction.reesGrade I) (reesGenerator I a) = ⊤ := by
  apply top_le_iff.mp
  rw [← affineBlowup_chart_cover I]
  exact iSup_le (fun b => Proj.basicOpen_mono (ReesGrading.Construction.reesGrade I) (reesGenerator I a) (reesGenerator I b)
    (reesGenerator_dvd_of_isUnit I a ha b))

/-- The structural morphism of a blowup on a standard chart is induced by
the coefficient-ring map already used to identify that chart. -/
theorem affineBlowup_chart_structureMap (a : I) :
    Proj.awayι (ReesGrading.Construction.reesGrade I) (reesGenerator I a) (reesGenerator_mem I a) (by decide) ≫
      ReesGrading.Construction.affineBlowupToSpec I = Spec.map (CommRingCat.ofHom (blowupChartConstants I a)) := by
  rw [ReesGrading.Construction.affineBlowupToSpec, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- Blowing up an ideal containing a unit is an isomorphism. -/
theorem affineBlowupToSpec_isIso_of_isUnit (a : I) (ha : IsUnit a.val) :
    IsIso (ReesGrading.Construction.affineBlowupToSpec I) := by
  let j : Spec (.of (blowupChart I a)) ⟶ ReesGrading.Construction.affineBlowup I :=
    Proj.awayι (ReesGrading.Construction.reesGrade I) (reesGenerator I a) (reesGenerator_mem I a) (by decide)
  let : IsOpenImmersion j := by
    dsimp [j]
    infer_instance
  let : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j (by
    dsimp only [j]
    rw [Proj.opensRange_awayι]
    exact affineBlowup_unit_chart_eq_top I a ha)
  let φ : CommRingCat.of R ⟶ CommRingCat.of (blowupChart I a) :=
    CommRingCat.ofHom (blowupChartConstants I a)
  let : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr
    (blowupChartConstants_bijective_of_isUnit I a ha)
  have hj : j ≫ ReesGrading.Construction.affineBlowupToSpec I = Spec.map φ := affineBlowup_chart_structureMap I a
  let : IsIso (j ≫ ReesGrading.Construction.affineBlowupToSpec I) := by
    rw [hj]
    infer_instance
  exact IsIso.of_isIso_comp_left j (ReesGrading.Construction.affineBlowupToSpec I)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Charts.Construction
