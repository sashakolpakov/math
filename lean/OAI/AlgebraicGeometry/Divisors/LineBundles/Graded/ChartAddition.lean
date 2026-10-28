import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayIs

/-! # Chart Addition -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartAddition.BundleCycles

noncomputable section

section

/-! Addition of actual homogeneous fractions with a fixed denominator. -/

open _root_.HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem gradedAway_mk_add {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (n : ℕ)
    (a b : A) (ha : a ∈ 𝒜 (n • k)) (hb : b ∈ 𝒜 (n • k)) :
    Away.mk 𝒜 hs n (a + b) (add_mem ha hb) = Away.mk 𝒜 hs n a ha + Away.mk 𝒜 hs n b hb := by
  apply HomogeneousLocalization.val_injective
  rw [val_add, Away.val_mk, Away.val_mk, Away.val_mk]
  simp only [Localization.mk_eq_mk']
  apply (IsLocalization.map_units (M := Submonoid.powers s) (Localization.Away s) ⟨s ^ n, ⟨n, rfl⟩⟩).mul_right_cancel
  rw [add_mul, IsLocalization.mk'_spec, IsLocalization.mk'_spec, IsLocalization.mk'_spec, map_add]

theorem gradedAway_mk_algebraMap {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (a : 𝒜 0) :
    Away.mk 𝒜 hs 0 a.val (by simpa only [zero_smul] using a.property) =
      fromZeroRingHom 𝒜 (Submonoid.powers s) a := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, AwayIs.BundleCycles.gradedFromZero_val]
  exact congrArg (Localization.mk a.val) (Subtype.ext (pow_zero s))

end

/-! The actual homogeneous fraction map is linear over the original
coefficient ring, with its canonical chart scalar map. -/

open _root_.HomogeneousLocalization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

def gradedChartScalarMap (s : A) : R →+* Away 𝒜 s :=
  (fromZeroRingHom 𝒜 (Submonoid.powers s)).comp (algebraMap R (𝒜 0))

abbrev gradedChartScalarAlgebra (s : A) : Algebra R (Away 𝒜 s) :=
  (gradedChartScalarMap 𝒜 s).toAlgebra

theorem gradedChartScalarMap_val (s : A) (r : R) :
    (gradedChartScalarMap 𝒜 s r).val = Localization.mk (algebraMap R A r) 1 :=
  AwayIs.BundleCycles.gradedFromZero_val 𝒜 s (algebraMap R (𝒜 0) r)

theorem gradedChartFraction_smul {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (n : ℕ)
    (r : R) (a : A) (ha : a ∈ 𝒜 (n • k)) :
    Away.mk 𝒜 hs n (r • a) ((𝒜 (n • k)).smul_mem r ha) =
      gradedChartScalarMap 𝒜 s r * Away.mk 𝒜 hs n a ha := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, Away.val_mk, gradedChartScalarMap_val, Away.val_mk, Localization.mk_mul]
  simp only [Algebra.smul_def, one_mul]

def gradedChartFractionLinear {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (n : ℕ) :
    letI := gradedChartScalarAlgebra 𝒜 s
    𝒜 (n • k) →ₗ[R] Away 𝒜 s := by
  let := gradedChartScalarAlgebra 𝒜 s
  exact {
    toFun a := Away.mk 𝒜 hs n a.val a.property
    map_add' a b := gradedAway_mk_add 𝒜 hs n a.val b.val a.property b.property
    map_smul' r a := gradedChartFraction_smul 𝒜 hs n r a.val a.property }

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartAddition.BundleCycles
