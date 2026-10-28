import Mathlib

/-! # Exterior Line -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorLine.Construction

noncomputable section

section

/-! Recovery of a subspace from the exterior product of a basis. -/

open scoped Classical TensorProduct
open Set

theorem exteriorPower_ιMulti_ne_zero
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {n : ℕ} {v : Fin n → V} (hv : LinearIndependent k v) :
    exteriorPower.ιMulti k n v ≠ 0 := by
  let W := Submodule.span k (range v)
  let b : Module.Basis (Fin n) k W := Module.Basis.span hv
  have hb : W.subtype ∘ b = v := by
    funext i
    exact congrArg Subtype.val (Module.Basis.span_apply hv i)
  have hn : exteriorPower.ιMulti k n b ≠ 0 := by
    intro hz
    have hh := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) hz
    exact one_ne_zero (by simpa only [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      Module.Basis.det_self, map_zero] using hh)
  rw [← hb, ← exteriorPower.map_apply_ιMulti]
  exact (map_ne_zero_iff _
    (exteriorPower.map_injective_field (n := n) W.injective_subtype)).mpr hn

theorem exteriorAlgebra_ιMulti_eq_zero_iff
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {n : ℕ} (v : Fin n → V) :
    ExteriorAlgebra.ιMulti k n v = 0 ↔ ¬LinearIndependent k v := by
  constructor
  · intro hz hv
    exact exteriorPower_ιMulti_ne_zero hv (Subtype.ext hz)
  · exact (ExteriorAlgebra.ιMulti k n).map_linearDependent v

theorem exterior_basis_annihilator
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {n : ℕ} {v : Fin n → V} (hv : LinearIndependent k v) (x : V) :
    ExteriorAlgebra.ι k x * ExteriorAlgebra.ιMulti k n v = 0 ↔
      x ∈ Submodule.span k (range v) := by
  have heq : ExteriorAlgebra.ιMulti k (n + 1) (Fin.cons x v) =
      ExteriorAlgebra.ι k x * ExteriorAlgebra.ιMulti k n v := by
    simp [Matrix.vecTail]
  rw [← heq, exteriorAlgebra_ιMulti_eq_zero_iff, linearIndependent_finCons]
  simp [hv]

theorem exterior_smul_of_mem_span
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {n : ℕ} {v : Fin n → V} (hv : LinearIndependent k v)
    (w : Fin n → V) (hw : ∀ i, w i ∈ Submodule.span k (range v)) :
    ∃ c : k, ExteriorAlgebra.ιMulti k n w = c • ExteriorAlgebra.ιMulti k n v := by
  let W := Submodule.span k (range v)
  let b : Module.Basis (Fin n) k W := Module.Basis.span hv
  let : FiniteDimensional k W := b.finiteDimensional_of_finite
  have hdim : Module.finrank k (⋀[k]^n W) = 1 := by
    rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b, Fintype.card_fin,
      Nat.choose_self]
  let u : Fin n → W := fun i => ⟨w i, hw i⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (exteriorPower.ιMulti k n b) (exteriorPower_ιMulti_ne_zero b.linearIndependent)).mp
      hdim (exteriorPower.ιMulti k n u)
  have hm := congrArg (exteriorPower.map n W.subtype) hc
  have hb : W.subtype ∘ b = v := by
    funext i
    exact congrArg Subtype.val (Module.Basis.span_apply hv i)
  simp only [map_smul, exteriorPower.map_apply_ιMulti, hb] at hm
  exact ⟨c, (congrArg Subtype.val hm).symm⟩

theorem span_eq_iff_exterior_smul
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {n : ℕ} {v w : Fin n → V} (hv : LinearIndependent k v) (hw : LinearIndependent k w) :
    Submodule.span k (range w) = Submodule.span k (range v) ↔
      ∃ c : k, c ≠ 0 ∧ ExteriorAlgebra.ιMulti k n w = c • ExteriorAlgebra.ιMulti k n v := by
  constructor
  · intro hspan
    obtain ⟨c, hc⟩ := exterior_smul_of_mem_span hv w (fun i =>
      hspan ▸ Submodule.subset_span (mem_range_self i))
    refine ⟨c, ?_, hc⟩
    intro hzero
    rw [hzero, zero_smul] at hc
    exact ((exteriorAlgebra_ιMulti_eq_zero_iff w).mp hc) hw
  · rintro ⟨c, hc, hmul⟩
    apply Submodule.ext
    intro x
    rw [← exterior_basis_annihilator hw x, ← exterior_basis_annihilator hv x, hmul,
      mul_smul_comm, smul_eq_zero]
    simp only [hc, false_or]

end

/-! Dual coordinates for a finite independent family recover the scalar
by which an exterior line is acted on. -/

open scoped Classical

theorem exists_dual_coordinates
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {r : ℕ}
    (v : Fin r → V) (hv : LinearIndependent k v) :
    ∃ φ : Fin r → Module.Dual k V,
      ∀ i j, φ j (v i) = (1 : Matrix (Fin r) (Fin r) k) i j := by
  obtain ⟨l, hl⟩ := (Fintype.linearCombination k v).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective)
  refine ⟨fun j => (LinearMap.proj j).comp l, ?_⟩
  intro i j
  have he := LinearMap.congr_fun hl (Pi.single i (1 : k))
  simp only [LinearMap.comp_apply, Fintype.linearCombination_apply_single, one_smul,
    LinearMap.id_apply] at he
  change l (v i) j = _
  rw [he]
  simp [Pi.single_apply, Matrix.one_apply, eq_comm]

theorem exterior_scalar_eq_determinant
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {r : ℕ}
    (v w : Fin r → V) (φ : Fin r → Module.Dual k V)
    (hφ : ∀ i j, φ j (v i) = (1 : Matrix (Fin r) (Fin r) k) i j)
    (c : k) (hc : ExteriorAlgebra.ιMulti k r w = c • ExteriorAlgebra.ιMulti k r v) :
    (Matrix.of (fun i j => φ j (w i))).det = c := by
  have he : exteriorPower.ιMulti k r w = c • exteriorPower.ιMulti k r v := Subtype.ext hc
  have hh := congrArg (exteriorPower.alternatingMapToDual k V r φ) he
  rw [map_smul, exteriorPower.alternatingMapToDual_apply_ιMulti,
    exteriorPower.alternatingMapToDual_apply_ιMulti] at hh
  have hm : Matrix.of (fun i j => φ j (v i)) = 1 := by
    ext i j
    exact hφ i j
  rw [hm, Matrix.det_one, smul_eq_mul, mul_one] at hh
  exact hh

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorLine.Construction
