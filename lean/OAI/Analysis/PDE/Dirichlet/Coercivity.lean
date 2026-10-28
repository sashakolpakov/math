import OAI.Analysis.PDE.Dirichlet.Symbol

open Set Metric
open scoped Matrix ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- A compact family of strictly positive continuous quadratic symbols has a
uniform positive ellipticity constant. -/
theorem uniform_positive_quadratic_lower
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    (hsphere : (sphere (0 : E) 1).Nonempty) (q : X → E → ℝ)
    (hq : ContinuousOn (fun p : X × E ↦ q p.1 p.2) (K ×ˢ sphere 0 1))
    (hpos : ∀ x ∈ K, ∀ v ≠ 0, 0 < q x v)
    (hscale : ∀ x ∈ K, ∀ (r : ℝ) v, q x (r • v) = r ^ 2 * q x v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ q x v := by
  obtain ⟨p, hp, hmin⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_isMinOn
    (hKne.prod hsphere) hq
  have hpnorm : ‖p.2‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hp.2
  have hpne : p.2 ≠ 0 := by intro h; simp [h] at hpnorm
  refine ⟨q p.1 p.2, hpos p.1 hp.1 p.2 hpne, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    have hz := hscale x hx 0 (0 : E)
    simpa using hz.ge
  · let u : E := ‖v‖⁻¹ • v
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, norm_ne_zero_iff.mpr hv]
    have hvu : ‖v‖ • u = v := by simp [u, smul_smul, norm_ne_zero_iff.mpr hv]
    have hqu : q p.1 p.2 ≤ q x u :=
      hmin (show (x, u) ∈ K ×ˢ sphere 0 1 from
        ⟨hx, by simpa only [mem_sphere, dist_zero_right] using hu⟩)
    calc
      q p.1 p.2 * ‖v‖ ^ 2 ≤ q x u * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hqu (sq_nonneg _)
      _ = q x (‖v‖ • u) := (mul_comm _ _).trans (hscale x hx ‖v‖ u).symm
      _ = q x v := by rw [hvu]

/-- The matching uniform upper bound needs only continuity and quadratic homogeneity. -/
theorem uniform_quadratic_upper
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    (hsphere : (sphere (0 : E) 1).Nonempty) (q : X → E → ℝ)
    (hq : ContinuousOn (fun p : X × E ↦ q p.1 p.2) (K ×ˢ sphere 0 1))
    (hscale : ∀ x ∈ K, ∀ (r : ℝ) v, q x (r • v) = r ^ 2 * q x v) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ v, q x v ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨p, hp, hmax⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_isMaxOn
    (hKne.prod hsphere) hq
  refine ⟨|q p.1 p.2| + 1, by positivity, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    have hz := hscale x hx 0 (0 : E)
    simpa using hz.le
  · let u : E := ‖v‖⁻¹ • v
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, norm_ne_zero_iff.mpr hv]
    have hvu : ‖v‖ • u = v := by simp [u, smul_smul, norm_ne_zero_iff.mpr hv]
    have hqu : q x u ≤ |q p.1 p.2| + 1 :=
      (hmax (show (x, u) ∈ K ×ˢ sphere 0 1 from
        ⟨hx, by simpa only [mem_sphere, dist_zero_right] using hu⟩)).trans
        ((le_abs_self _).trans (by linarith))
    calc
      q x v = q x (‖v‖ • u) := by rw [hvu]
      _ = ‖v‖ ^ 2 * q x u := hscale x hx ‖v‖ u
      _ ≤ ‖v‖ ^ 2 * (|q p.1 p.2| + 1) := mul_le_mul_of_nonneg_left hqu (sq_nonneg _)
      _ = (|q p.1 p.2| + 1) * ‖v‖ ^ 2 := mul_comm _ _

def inversePrincipalSymbol {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (ξ : CoordinateSpace n s) : ℝ :=
  (quaternionForm C (OAI.Analysis.Calculus.Quaternion.gradientMap e ξ)).re

theorem gradientMap_real_smul {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (r : ℝ) (ξ : CoordinateSpace n s) :
    OAI.Analysis.Calculus.Quaternion.gradientMap e (r • ξ) = r • OAI.Analysis.Calculus.Quaternion.gradientMap e ξ := by
  funext a
  simp [OAI.Analysis.Calculus.Quaternion.gradientMap, Finset.smul_sum, smul_smul, PiLp.smul_apply]

theorem quaternionForm_smul_vector {n : ℕ} (C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (r : ℝ) (g : Fin n → Quaternion ℝ) :
    quaternionForm C (r • g) = r ^ 2 • quaternionForm C g := by
  simp [quaternionForm, Pi.smul_apply, smul_smul, Finset.smul_sum, pow_two]

theorem inversePrincipalSymbol_smul {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (r : ℝ) (ξ : CoordinateSpace n s) :
    inversePrincipalSymbol e C (r • ξ) = r ^ 2 * inversePrincipalSymbol e C ξ := by
  simp only [inversePrincipalSymbol, gradientMap_real_smul, quaternionForm_smul_vector]
  rfl

theorem continuous_inversePrincipalSymbol {n s : ℕ} (e : Fin s → Quaternion ℝ) :
    Continuous (fun p : Matrix (Fin n) (Fin n) (Quaternion ℝ) × CoordinateSpace n s ↦
      inversePrincipalSymbol e p.1 p.2) := by
  unfold inversePrincipalSymbol quaternionForm OAI.Analysis.Calculus.Quaternion.gradientMap
  apply Quaternion.continuous_re.comp
  fun_prop

theorem inversePrincipalSymbol_pos {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (he : Function.Injective (OAI.Analysis.Calculus.Quaternion.gradientMap (m := Fin n) e))
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hC : (OAI.LinearAlgebra.Moore.complexify C).PosDef)
    (ξ : CoordinateSpace n s) (hξ : ξ ≠ 0) : 0 < inversePrincipalSymbol e C ξ := by
  apply (OAI.LinearAlgebra.Moore.complexify_posDef_iff (OAI.LinearAlgebra.Moore.isHermitian_of_complexify hC.isHermitian)).mp hC
  intro hg
  have hzero : OAI.Analysis.Calculus.Quaternion.gradientMap e (0 : Fin n × Fin s → ℝ) = 0 := by
    funext a
    simp [OAI.Analysis.Calculus.Quaternion.gradientMap]
  have hfun : (ξ : Fin n × Fin s → ℝ) = 0 := he (hg.trans hzero.symm)
  exact hξ (by ext i; exact congrFun hfun i)

theorem inversePrincipalSymbol_eq_trace {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (ξ : CoordinateSpace n s) :
    inversePrincipalSymbol e C ξ =
      ∑ i, ((C * OAI.Analysis.Calculus.Quaternion.hessianMap e (fun i j ↦ ξ i * ξ j)) i i).re := by
  rw [OAI.Analysis.Calculus.Quaternion.hessianMap_rankOne, quaternionRealTrace_outer]
  rfl

theorem fourSlot_unitSphere_nonempty {n : ℕ} (hn : 1 ≤ n) :
    (sphere (0 : CoordinateSpace n 4) 1).Nonempty := by
  let i : Fin n × Fin 4 := (⟨0, by omega⟩, 0)
  refine ⟨coordinateVector i, ?_⟩
  simp [coordinateVector]

theorem continuous_inversePrincipalSymbol_field {X : Type*} [TopologicalSpace X]
    {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (C : X → Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hC : Continuous C) :
    Continuous (fun p : X × CoordinateSpace n s ↦ inversePrincipalSymbol e (C p.1) p.2) := by
  unfold inversePrincipalSymbol quaternionForm OAI.Analysis.Calculus.Quaternion.gradientMap
  apply Quaternion.continuous_re.comp
  fun_prop

theorem inversePrincipalSymbol_uniform_bound {X : Type*} [TopologicalSpace X]
    {n : ℕ} (hn : 1 ≤ n) {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    (C : X → Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hC : Continuous C)
    (hpos : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (C x)).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ ξ : CoordinateSpace n 4,
      c * ‖ξ‖ ^ 2 ≤ inversePrincipalSymbol OAI.Analysis.Calculus.Quaternion.fourSlots (C x) ξ := by
  let q : X → CoordinateSpace n 4 → ℝ := fun x ξ ↦ inversePrincipalSymbol OAI.Analysis.Calculus.Quaternion.fourSlots (C x) ξ
  have hq : ContinuousOn (fun p : X × CoordinateSpace n 4 ↦ q p.1 p.2)
      (K ×ˢ sphere 0 1) := (continuous_inversePrincipalSymbol_field OAI.Analysis.Calculus.Quaternion.fourSlots C hC).continuousOn
  have hp : ∀ x ∈ K, ∀ ξ ≠ 0, 0 < q x ξ := by
    intro x hx ξ hξ
    exact inversePrincipalSymbol_pos OAI.Analysis.Calculus.Quaternion.fourSlots OAI.Analysis.Calculus.Quaternion.gradientMap_fourSlots_injective (C x) (hpos x hx) ξ hξ
  have hs : ∀ x ∈ K, ∀ (r : ℝ) ξ, q x (r • ξ) = r ^ 2 * q x ξ := by
    intro x hx r ξ
    exact inversePrincipalSymbol_smul OAI.Analysis.Calculus.Quaternion.fourSlots (C x) r ξ
  exact uniform_positive_quadratic_lower hK hKne (fourSlot_unitSphere_nonempty hn) q hq hp hs

theorem inversePrincipalSymbol_uniform_upper_bound {X : Type*} [TopologicalSpace X]
    {n : ℕ} (hn : 1 ≤ n) {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    (C : X → Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hC : Continuous C) :
    ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K, ∀ ξ : CoordinateSpace n 4,
      inversePrincipalSymbol OAI.Analysis.Calculus.Quaternion.fourSlots (C x) ξ ≤ b * ‖ξ‖ ^ 2 := by
  let q : X → CoordinateSpace n 4 → ℝ := fun x ξ ↦ inversePrincipalSymbol OAI.Analysis.Calculus.Quaternion.fourSlots (C x) ξ
  have hq : ContinuousOn (fun p : X × CoordinateSpace n 4 ↦ q p.1 p.2)
      (K ×ˢ sphere 0 1) := (continuous_inversePrincipalSymbol_field OAI.Analysis.Calculus.Quaternion.fourSlots C hC).continuousOn
  have hs : ∀ x ∈ K, ∀ (r : ℝ) ξ, q x (r • ξ) = r ^ 2 * q x ξ := by
    intro x hx r ξ
    exact inversePrincipalSymbol_smul OAI.Analysis.Calculus.Quaternion.fourSlots (C x) r ξ
  exact uniform_quadratic_upper hK hKne (fourSlot_unitSphere_nonempty hn) q hq hs

/-- Uniform ellipticity of a continuous positive inverse-Hessian field on a
compact set, for the exact real rank-one symbol of the four-slot operator. -/
theorem inversePrincipalSymbol_uniform_lower {X : Type*} [TopologicalSpace X]
    {n : ℕ} (hn : 1 ≤ n) {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    (C : X → Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hC : Continuous C)
    (hpos : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (C x)).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ ξ : CoordinateSpace n 4,
      c * ‖ξ‖ ^ 2 ≤ ∑ i, ((C x * OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j ↦ ξ i * ξ j)) i i).re := by
  obtain ⟨c, hcpos, hc⟩ := inversePrincipalSymbol_uniform_bound hn hK hKne C hC hpos
  refine ⟨c, hcpos, ?_⟩
  intro x hx ξ
  simpa only [inversePrincipalSymbol_eq_trace] using hc x hx ξ

/-- Both constants in the usual uniform ellipticity condition are obtained
from compactness, for the actual inverse-Hessian trace symbol. -/
theorem inversePrincipalSymbol_uniform_elliptic {X : Type*} [TopologicalSpace X]
    {n : ℕ} (hn : 1 ≤ n) {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    (C : X → Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hC : Continuous C)
    (hpos : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (C x)).PosDef) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x ∈ K, ∀ ξ : CoordinateSpace n 4,
      a * ‖ξ‖ ^ 2 ≤ ∑ i, ((C x * OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j ↦ ξ i * ξ j)) i i).re ∧
      (∑ i, ((C x * OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j ↦ ξ i * ξ j)) i i).re) ≤ b * ‖ξ‖ ^ 2 := by
  obtain ⟨a, ha, hal⟩ := inversePrincipalSymbol_uniform_bound hn hK hKne C hC hpos
  obtain ⟨b, hb, hbu⟩ := inversePrincipalSymbol_uniform_upper_bound hn hK hKne C hC
  refine ⟨a, b, ha, hb, ?_⟩
  intro x hx ξ
  simpa only [inversePrincipalSymbol_eq_trace] using And.intro (hal x hx ξ) (hbu x hx ξ)

end OAI.Analysis.PDE.Dirichlet
