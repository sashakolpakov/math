import Mathlib

/-! # Compact -/

namespace OAI.Topology.Pontryagin.Compact.Constructions.CharacterExtension

noncomputable section

/-! CharacterExtension: extension from a compact group using character separation and
Stone–Weierstrass. All supporting claims in this file are proved. -/

open _root_.MeasureTheory Set _root_.Topology
open scoped ComplexConjugate Pointwise

variable {G K : Type*} [CommGroup G] [TopologicalSpace G]
  [CommGroup K] [TopologicalSpace K]

/-- Restrict a unitary character and regard it as a complex continuous function. -/
def restrictChar (ι : K →ₜ* G) (χ : PontryaginDual G) : C(K, ℂ) where
  toFun x := (χ (ι x) : ℂ)
  continuous_toFun := continuous_subtype_val.comp (χ.continuous.comp ι.continuous)

@[simp] theorem restrictChar_apply (ι : K →ₜ* G) (χ : PontryaginDual G) (x : K) :
    restrictChar ι χ x = (χ (ι x) : ℂ) := rfl

@[simp] theorem restrictChar_one (ι : K →ₜ* G) : restrictChar ι 1 = 1 := by
  ext x
  simp [restrictChar]

@[simp] theorem restrictChar_mul (ι : K →ₜ* G) (χ ψ : PontryaginDual G) :
    restrictChar ι (χ * ψ) = restrictChar ι χ * restrictChar ι ψ := by
  ext x
  exact Circle.coe_mul (χ (ι x)) (ψ (ι x))

@[simp] theorem restrictChar_inv (ι : K →ₜ* G) (χ : PontryaginDual G) :
    restrictChar ι χ⁻¹ = star (restrictChar ι χ) := by
  ext x
  exact Circle.coe_inv_eq_conj (χ (ι x))

def restrictionMonoid (ι : K →ₜ* G) : Submonoid C(K, ℂ) where
  carrier := range (restrictChar ι)
  one_mem' := ⟨1, restrictChar_one ι⟩
  mul_mem' := by
    rintro _ _ ⟨χ, rfl⟩ ⟨ψ, rfl⟩
    exact ⟨χ * ψ, restrictChar_mul ι χ ψ⟩

lemma star_restrictionMonoid (ι : K →ₜ* G) :
    star (restrictionMonoid ι : Set C(K, ℂ)) = restrictionMonoid ι := by
  ext f
  change (∃ χ, restrictChar ι χ = star f) ↔ ∃ χ, restrictChar ι χ = f
  constructor
  · rintro ⟨χ, hχ⟩
    exact ⟨χ⁻¹, by rw [restrictChar_inv, hχ, star_star]⟩
  · rintro ⟨χ, hχ⟩
    exact ⟨χ⁻¹, by rw [restrictChar_inv, hχ]⟩

lemma restrictionAlgebra_span (ι : K →ₜ* G) :
    (StarAlgebra.adjoin ℂ (restrictionMonoid ι : Set C(K, ℂ))).toSubalgebra.toSubmodule =
      Submodule.span ℂ (restrictionMonoid ι : Set C(K, ℂ)) := by
  rw [StarAlgebra.adjoin_eq_span, star_restrictionMonoid, union_self,
    Submonoid.closure_eq]

section Integral

variable [CompactSpace K] [IsTopologicalGroup K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]

/-- Integration against a fixed character is a continuous linear functional. -/
def characterCoefficient (ψ : K →ₜ* Circle) : C(K, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x * conj (ψ x : ℂ) ∂μ
      map_add' := by
        intro f g
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add
          ((f.continuous.mul (Complex.continuous_conj.comp
            (continuous_subtype_val.comp ψ.continuous))).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _))
          ((g.continuous.mul (Complex.continuous_conj.comp
            (continuous_subtype_val.comp ψ.continuous))).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _))
      map_smul' := by
        intro c f
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
    (μ.real univ) (fun f => by
      calc ‖∫ x, f x * conj (ψ x : ℂ) ∂μ‖
          ≤ ∫ x, ‖f‖ ∂μ := norm_integral_le_of_norm_le (integrable_const _)
            (Filter.Eventually.of_forall fun x => by
              simpa only [norm_mul, Complex.norm_conj, Circle.norm_coe, mul_one]
                using f.norm_coe_le_norm x)
        _ = μ.real univ * ‖f‖ := by simp)

omit [CompactSpace K] [T2Space K] [IsFiniteMeasure μ] in
lemma integral_character_eq_zero [μ.IsMulLeftInvariant] (θ : K →ₜ* Circle)
    (hθ : θ ≠ 1) : (∫ x, (θ x : ℂ) ∂μ) = 0 := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hθ
  have hx' : (θ x : ℂ) ≠ 1 := by
    intro h
    apply hx
    apply Circle.coe_injective
    exact h
  have h := integral_mul_left_eq_self (μ := μ) (fun y => (θ y : ℂ)) x
  simp only [map_mul, Circle.coe_mul, integral_const_mul] at h
  by_contra hne
  exact hx' ((mul_eq_right₀ hne).mp h)

end Integral

/-- Point-separating characters extend every character on an injected compact group. -/
theorem compact_character_extension
    [CompactSpace K] [IsTopologicalGroup K] [T2Space K]
    (hsep : ∀ x y : G, x ≠ y → ∃ χ : PontryaginDual G, χ x ≠ χ y)
    (ι : K →ₜ* G) (hι : Function.Injective ι) (ψ : K →ₜ* Circle) :
    ∃ χ : PontryaginDual G, ∀ x : K, χ (ι x) = ψ x := by
  classical
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts K) := inferInstance
  let μ := Measure.haarMeasure K₀
  let A := StarAlgebra.adjoin ℂ (restrictionMonoid ι : Set C(K, ℂ))
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨χ, hχ⟩ := hsep (ι x) (ι y) (fun h => hxy (hι h))
    refine ⟨restrictChar ι χ, ⟨restrictChar ι χ, ?_, rfl⟩, ?_⟩
    · exact StarAlgebra.subset_adjoin ℂ _ ⟨χ, rfl⟩
    · exact fun h => hχ (Circle.coe_injective h)
  have hdense := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  let F := characterCoefficient μ ψ
  by_contra hn
  have hne : ∀ χ : PontryaginDual G, (χ : G →ₜ* Circle).comp ι ≠ ψ := by
    intro χ heq
    apply hn
    exact ⟨χ, fun x => DFunLike.congr_fun heq x⟩
  have hvanish : ∀ χ : PontryaginDual G, F (restrictChar ι χ) = 0 := by
    intro χ
    let θ : K →ₜ* Circle := (χ : G →ₜ* Circle).comp ι * ψ⁻¹
    have hθ : θ ≠ 1 := by
      intro h
      exact hne χ (mul_inv_eq_one.mp h)
    have hz := integral_character_eq_zero μ θ hθ
    change (∫ x, (χ (ι x) : ℂ) * conj (ψ x : ℂ) ∂μ) = 0
    convert hz using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (χ (ι x) : ℂ) * conj (ψ x : ℂ) = ↑(χ (ι x) * (ψ x)⁻¹)
      rw [Circle.coe_mul, Circle.coe_inv_eq_conj]
  have hsub : (A : Set C(K, ℂ)) ⊆ F.ker := by
    change A.toSubalgebra.toSubmodule ≤ F.ker
    rw [show A.toSubalgebra.toSubmodule = _ from restrictionAlgebra_span ι]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    exact hvanish χ
  let ψc : C(K, ℂ) := ⟨fun x => (ψ x : ℂ), continuous_subtype_val.comp ψ.continuous⟩
  have hmem : ψc ∈ closure (A : Set C(K, ℂ)) := by
    change ψc ∈ A.topologicalClosure
    rw [hdense]
    trivial
  have hzero : F ψc = 0 := closure_minimal hsub F.isClosed_ker hmem
  have hmass : 0 < μ.real univ := by
    exact ENNReal.toReal_pos (isOpen_univ.measure_pos μ univ_nonempty).ne'
      (measure_ne_top μ univ)
  have heq : F ψc = (μ.real univ : ℂ) := by
    change (∫ x, (ψ x : ℂ) * conj (ψ x : ℂ) ∂μ) = _
    simp only [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
    simp
  rw [heq] at hzero
  exact (ne_of_gt hmass) (Complex.ofReal_eq_zero.mp hzero)

end

end OAI.Topology.Pontryagin.Compact.Constructions.CharacterExtension
