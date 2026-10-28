import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Localization Flat -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert

noncomputable section

/-!
Flatness of a homogeneous affine chart follows from flatness of the
sufficiently high graded pieces. Finite relations admit a common
denominator, and become relations in one high graded piece after one
further multiplication by the chart coordinate.
-/

open _root_.HomogeneousLocalization

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

instance homogeneousLocalizationModule (P : Submonoid A) :
    Module R (HomogeneousLocalization 𝒜 P) :=
  Function.Injective.module R ⟨⟨HomogeneousLocalization.val, HomogeneousLocalization.val_zero⟩,
    HomogeneousLocalization.val_add⟩ (HomogeneousLocalization.val_injective P)
      (HomogeneousLocalization.val_smul P)

instance homogeneousLocalizationBaseAlgebra (P : Submonoid A) :
    Algebra R (HomogeneousLocalization 𝒜 P) :=
  Algebra.ofModule
    (fun r x y => HomogeneousLocalization.val_injective P (by
      simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_smul, smul_mul_assoc]))
    (fun r x y => HomogeneousLocalization.val_injective P (by
      simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_smul, mul_smul_comm]))

theorem homogeneousLocalization_algebraMap (P : Submonoid A) :
    algebraMap R (HomogeneousLocalization 𝒜 P) =
      (HomogeneousLocalization.fromZeroRingHom 𝒜 P).comp (algebraMap R (𝒜 0)) := by
  apply RingHom.ext
  intro r
  apply HomogeneousLocalization.val_injective
  rw [Algebra.algebraMap_eq_smul_one, HomogeneousLocalization.val_smul,
    HomogeneousLocalization.val_one]
  change r • (1 : Localization P) = Localization.mk ((algebraMap R (𝒜 0) r).val) 1
  rw [Localization.mk_eq_mk', IsLocalization.mk'_one]
  rw [Algebra.algebraMap_eq_smul_one (R := R) (A := 𝒜 0)]
  change r • (1 : Localization P) = algebraMap A (Localization P) (r • 1)
  simp only [Algebra.smul_def, mul_one]
  exact IsScalarTower.algebraMap_apply R A (Localization P) r

variable {𝒜} {s : A} (hs : s ∈ 𝒜 1)

def degreeFraction (d : ℕ) (f : 𝒜 d) : HomogeneousLocalization.Away 𝒜 s :=
  HomogeneousLocalization.Away.mk 𝒜 hs d f.val (by simpa only [smul_eq_mul, mul_one] using f.property)

theorem val_degreeFraction (d : ℕ) (f : 𝒜 d) :
    (degreeFraction hs d f).val = algebraMap A (Localization.Away s) f.val *
      IsLocalization.Away.invSelf s ^ d := by
  erw [degreeFraction, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  rw [map_pow, mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf s),
    IsLocalization.Away.mul_invSelf, one_pow, mul_one]

def degreeFractionLinear (d : ℕ) : 𝒜 d →ₗ[R] HomogeneousLocalization.Away 𝒜 s where
  toFun := degreeFraction hs d
  map_add' f g := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_add, val_degreeFraction, val_degreeFraction, val_degreeFraction]
    simp only [Submodule.coe_add, map_add, add_mul]
  map_smul' r f := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_smul, val_degreeFraction, val_degreeFraction]
    simp only [Submodule.coe_smul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      IsScalarTower.smul_assoc]
    rfl

def degreeTransition (d e : ℕ) (hde : d ≤ e) : 𝒜 d →ₗ[R] 𝒜 e where
  toFun f := ⟨s ^ (e - d) * f.val, by
    have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded (e - d) hs) f.property
    simpa only [smul_eq_mul, mul_one, Nat.sub_add_cancel hde] using h⟩
  map_add' f g := Subtype.ext (mul_add _ _ _)
  map_smul' r f := Subtype.ext (mul_smul_comm _ _ _)

theorem degreeFraction_transition (d e : ℕ) (hde : d ≤ e) (f : 𝒜 d) :
    degreeFractionLinear hs e (degreeTransition hs d e hde f) = degreeFractionLinear hs d f := by
  apply HomogeneousLocalization.val_injective
  change (degreeFraction hs e _).val = (degreeFraction hs d f).val
  erw [degreeFraction, degreeFraction, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  change 1 * (s ^ d * (s ^ (e - d) * f.val)) = 1 * (s ^ e * f.val)
  rw [one_mul, one_mul, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hde]

theorem degreeFraction_eq_zero_iff (d : ℕ) (f : 𝒜 d) :
    degreeFractionLinear hs d f = 0 ↔ ∃ k : ℕ, s ^ k * f.val = 0 := by
  change degreeFraction hs d f = 0 ↔ _
  erw [degreeFraction, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.val_zero, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨k, hk⟩ := t.property
    rw [← hk] at ht
    exact ⟨k, ht⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨s ^ k, ⟨k, rfl⟩⟩, hk⟩

theorem degreeFraction_common_denominator {ι : Type*} [Fintype ι]
    (x : ι → HomogeneousLocalization.Away 𝒜 s) (N : ℕ) :
    ∃ d ≥ N, ∃ f : ι → 𝒜 d, ∀ i, degreeFractionLinear hs d (f i) = x i := by
  classical
  have hx (i : ι) : ∃ d : ℕ, ∃ f : 𝒜 d, degreeFractionLinear hs d f = x i := by
    obtain ⟨d, f, hf, hfx⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hs (x i)
    have hf' : f ∈ 𝒜 d := by simpa only [smul_eq_mul, mul_one] using hf
    exact ⟨d, ⟨f, hf'⟩, hfx⟩
  choose b f hf using hx
  let d := max N (Finset.univ.sup b)
  have hb (i : ι) : b i ≤ d :=
    (Finset.le_sup (f := b) (Finset.mem_univ i)).trans (le_max_right _ _)
  refine ⟨d, le_max_left _ _, fun i => degreeTransition hs (b i) d (hb i) (f i), fun i => ?_⟩
  exact (degreeFraction_transition hs (b i) d (hb i) (f i)).trans (hf i)

include hs in
/-- A chart of a graded algebra is flat over the coefficient ring if its
sufficiently high homogeneous pieces are flat. -/
theorem homogeneousLocalization_flat_of_eventually_flat
    (N : ℕ) (hflat : ∀ d ≥ N, Module.Flat R (𝒜 d)) :
    Module.Flat R (HomogeneousLocalization.Away 𝒜 s) := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro l a x hx
  obtain ⟨d, hd, f, hf⟩ := degreeFraction_common_denominator hs x N
  have hsum : degreeFractionLinear hs d (∑ i, a i • f i) = 0 := by
    simpa only [map_sum, map_smul, hf] using hx
  obtain ⟨k, hk⟩ := (degreeFraction_eq_zero_iff hs d _).mp hsum
  let t := degreeTransition hs d (d + k) (Nat.le_add_right _ _)
  have ht : ∑ i, a i • t (f i) = 0 := by
    simp_rw [← map_smul]
    rw [← map_sum]
    apply Subtype.ext
    change s ^ (d + k - d) * (∑ i, a i • f i).val = 0
    simpa only [Nat.add_sub_cancel_left] using hk
  have : Module.Flat R (𝒜 (d + k)) := hflat _ (hd.trans (Nat.le_add_right _ _))
  obtain ⟨m, b, y, hxy, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero ht
  refine ⟨m, b, fun j => degreeFractionLinear hs (d + k) (y j), fun i => ?_, hb⟩
  have h := congrArg (degreeFractionLinear hs (d + k)) (hxy i)
  rw [map_sum] at h
  simp only [map_smul] at h
  exact ((degreeFraction_transition hs d (d + k) (Nat.le_add_right _ _) (f i)).trans (hf i)).symm.trans h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert
