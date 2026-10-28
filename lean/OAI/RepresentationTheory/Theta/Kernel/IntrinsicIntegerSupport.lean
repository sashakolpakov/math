import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz
import OAI.RepresentationTheory.Weil.AdelicSplitting.PositionBasis

/-! # Intrinsic Integer Support -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicIntegerSupport.Intrinsic

noncomputable section

/-! A native Schwartz input is supported on a scaled integer lattice at
rational positions. Integer multiples refine its finite-adelic period. -/

open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def scaledIntegers (r : 𝓞 F) : (Fin N → 𝓞 F) →ₗ[ℤ] (Fin N → F) where
  toFun u i := (algebraMap (𝓞 F) F r)⁻¹ * algebraMap (𝓞 F) F (u i)
  map_add' u v := by funext i; simp [mul_add]
  map_smul' c u := by funext i; simp [zsmul_eq_mul, mul_left_comm]

theorem native_support_integer_presentation (f : Adelic.FiniteSchwartz.finiteSchwartz F N) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ ∀ x : Fin N → F,
      Adelic.Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) ≠ 0 →
      ∃ u : Fin N → 𝓞 F, scaledIntegers F N r u = x := by
  obtain ⟨r,hr,hbound⟩ := Weil.AdelicSplitting.IntegralAdeles.Construction.compact_subset_finiteIntegralBox F
    (tsupport (Adelic.Evaluation.finiteSchwartzFunction F N f)) (Adelic.CompactSupport.AdelicSchwartz.finiteSchwartzFunction_mem F N f).2
  have hrF : algebraMap (𝓞 F) F r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hr
  refine ⟨r,hr,?_⟩
  intro x hx
  have hb := hbound (subset_tsupport _ hx)
  have hi (i : Fin N) : ∃ u : 𝓞 F,
      algebraMap (𝓞 F) F u = algebraMap (𝓞 F) F r * x i := by
    apply (Weil.AdelicSplitting.IntegralAdeles.Construction.rational_mem_finiteIntegral_iff F _).mp
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    exact hb i
  choose u hu using hi
  refine ⟨u,?_⟩
  funext i
  change (algebraMap (𝓞 F) F r)⁻¹ * algebraMap (𝓞 F) F (u i) = x i
  rw [hu i, ← mul_assoc, inv_mul_cancel₀ hrF, one_mul]

theorem scaledIntegers_translation (r : 𝓞 F) (hr : r ≠ 0) (m D : ℕ)
    (v : Fin N → 𝓞 F) :
    scaledIntegers F N r ((2 * (D : ℤ)) • (fun i => r * (m : 𝓞 F) * v i)) =
      fun i => (2 * D * m : F) * algebraMap (𝓞 F) F (v i) := by
  have hrF : algebraMap (𝓞 F) F r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hr
  funext i
  change (algebraMap (𝓞 F) F r)⁻¹ *
    algebraMap (𝓞 F) F ((2 * (D : ℤ)) • (r * (m : 𝓞 F) * v i)) = _
  simp only [zsmul_eq_mul, map_mul, map_natCast, map_ofNat, Int.cast_mul,
    Int.cast_ofNat, Int.cast_natCast]
  field_simp

theorem lattice_nat_multiple (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hdiv : m ∣ n) :
    Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (ι := Fin N) (n : F) (by exact_mod_cast hn.ne') ≤
      Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (m : F) (by exact_mod_cast hm.ne') := by
  let hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  rintro x ⟨v,hv,rfl⟩
  obtain ⟨k,hk⟩ := hdiv
  have hx : Weil.AdelicSplitting.FiniteLattices.Construction.finitePositionScale (m : F) v ∈ Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (m : F) hmF :=
    ⟨v,hv,rfl⟩
  have h := (Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (m : F) hmF).nsmul_mem hx k
  change Weil.AdelicSplitting.FiniteLattices.Construction.finitePositionScale (n : F) v ∈ _
  rw [Weil.AdelicSplitting.FiniteLattices.Construction.finitePositionScale_natCast, hk, mul_nsmul]
  simpa only [Weil.AdelicSplitting.FiniteLattices.Construction.finitePositionScale_natCast] using h

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicIntegerSupport.Intrinsic
