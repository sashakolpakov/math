import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateInjection

/-! # Tate Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateKernels.Construction

noncomputable section

/-! The intrinsic rational Tate preimage detects the actual finite
torsion kernel of a homomorphism. The proof uses coherent point lifts
and the proved integral-image divisibility criterion. -/

open scoped TensorProduct

universe u
variable (q : ℕ) [Fact q.Prime]
  {H H' H'' : Type u} [AddCommGroup H] [AddCommGroup H'] [AddCommGroup H'']

def rationalTateAddMap (f : H →+ H') :
    (ℚ_[q] ⊗[ℤ_[q]] TateComparison.Add.Tate.Module (H := H) q) →ₗ[ℚ_[q]]
      ℚ_[q] ⊗[ℤ_[q]] TateComparison.Add.Tate.Module (H := H') q := (TateComparison.Add.Tate.map q f).baseChange ℚ_[q]

def tateAddPreimage (f : H →+ H') :
    Submodule ℤ_[q] (ℚ_[q] ⊗[ℤ_[q]] TateComparison.Add.Tate.Module (H := H) q) :=
  (TateInjection.Construction.tateIntegralMap (H := H') q).range.comap ((rationalTateAddMap q f).restrictScalars ℤ_[q])

theorem rationalTateAddMap_integral (f : H →+ H') (x : TateComparison.Add.Tate.Module (H := H) q) :
    rationalTateAddMap q f (TateInjection.Construction.tateIntegralMap q x) = TateInjection.Construction.tateIntegralMap q (TateComparison.Add.Tate.map q f x) :=
  LinearMap.baseChange_tmul (A := ℚ_[q]) (f := TateComparison.Add.Tate.map q f) (a := 1) (x := x)

/-- Dividing an integral Tate lift by q^n lies in the target-lattice
preimage precisely when its n-th torsion point lies in the kernel. -/
theorem tate_fraction_mem_preimage_iff (f : H →+ H') (n : ℕ)
    (x : TateComparison.Add.Tate.Module (H := H) q) :
    ((q : ℚ_[q]) ^ n)⁻¹ • TateInjection.Construction.tateIntegralMap q x ∈ tateAddPreimage q f ↔
      f (x.val n).val = 0 := by
  have hq : (q : ℚ_[q]) ^ n ≠ 0 :=
    pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  have heval : TateTorsion.Construction.tateEvaluation q n (TateComparison.Add.Tate.map q f x) = 0 ↔ f (x.val n).val = 0 := by
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  change rationalTateAddMap q f (((q : ℚ_[q]) ^ n)⁻¹ • TateInjection.Construction.tateIntegralMap q x) ∈
    (TateInjection.Construction.tateIntegralMap (H := H') q).range ↔ _
  rw [map_smul, rationalTateAddMap_integral]
  constructor
  · rintro ⟨y, hy⟩
    apply heval.mp
    apply (TateInjection.Construction.tateEvaluation_zero_iff_rational_divisible q n (TateComparison.Add.Tate.map q f x)).mpr
    exact ⟨y, ((eq_inv_smul_iff₀ hq).mp hy).symm⟩
  · intro h
    obtain ⟨y, hy⟩ := (TateInjection.Construction.tateEvaluation_zero_iff_rational_divisible q n (TateComparison.Add.Tate.map q f x)).mp
      (heval.mpr h)
    exact ⟨y, (eq_inv_smul_iff₀ hq).mpr hy.symm⟩

/-- Equal full Tate preimage lattices give equal kernels on actual
q-power torsion points whenever those points admit coherent q-divisions. -/
theorem tate_preimage_eq_kernel_on_torsion
    (hdiv : ∀ x : H, ∃ y, q • y = x) (f : H →+ H') (g : H →+ H'')
    (hpre : tateAddPreimage q f = tateAddPreimage q g)
    (n : ℕ) (x : H) (hx : q ^ n • x = 0) : f x = 0 ↔ g x = 0 := by
  obtain ⟨y, hy⟩ := TateTorsion.Construction.tateEvaluation_surjective q hdiv n ⟨x, hx⟩
  have he : (y.val n).val = x := congrArg Subtype.val hy
  rw [← he, ← tate_fraction_mem_preimage_iff, ← tate_fraction_mem_preimage_iff, hpre]

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateKernels.Construction
