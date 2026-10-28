import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitCosetRelativePositions
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScalarCosetExponents
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution

/-! # Integral Type Uniqueness -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianScheme.TateComparison.IntegralTypeUniqueness

/-! Actual raw integral double cosets are disjoint: their shared
multiplier and all dominant block exponents are determined by a coset. -/

variable (s q : ℕ) [Fact q.Prime]

theorem integralType_eq_of_coordinates (u v : Local.IntegralType s)
    (hm : u.val.multiplier = v.val.multiplier) (ha : u.val.exponent = v.val.exponent) : u = v := by
  apply Subtype.ext
  rcases u with ⟨⟨mu, au, du⟩, hu⟩
  rcases v with ⟨⟨mv, av, dv⟩, hv⟩
  dsimp at hm ha ⊢
  cases hm
  cases ha
  rfl

theorem rawIntegralType_eq_of_common (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (u v : Local.IntegralType s) (x : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q)
    (hu : x ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q u.val))
    (hv : x ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q v.val)) : u = v := by
  obtain ⟨hu, hmu⟩ := (SplitCosetRelativePositions.splitRaw_support_iff_positions s q u x).mp hu
  obtain ⟨hv, hmv⟩ := (SplitCosetRelativePositions.splitRaw_support_iff_positions s q v x).mp hv
  have hm : u.val.multiplier = v.val.multiplier :=
    neg_inj.mp (ScalarCosetExponents.scalarCoset_qUnit_zpow_injective q (hmu.symm.trans hmv))
  apply integralType_eq_of_coordinates s u v hm
  funext i
  exact RelativePositionUniqueness.relativePosition_exponents_unique hElementaryDivisors (q : ℤ_[q]) PadicInt.irreducible_p _ _
    (u.val.exponent i) (v.val.exponent i) (u.val.dominant i) (v.val.dominant i) (hu i) (hv i)

end AlgebraicGeometry.AbelianScheme.TateComparison.IntegralTypeUniqueness

namespace AlgebraicGeometry.AbelianScheme.TateComparison

/-! A common central shift proves uniqueness of arbitrary dominant
raw types, including negative chosen and opposite exponents. -/

section

theorem Local.LocalType.shift_integral_mono {s : ℕ} (t : Local.LocalType s) {n m : ℕ}
    (hn : (t.shift n).IsIntegral) (hnm : n ≤ m) : (t.shift m).IsIntegral := by
  obtain ⟨hm, ha⟩ := hn
  refine ⟨?_, fun v i => ?_⟩
  · change 0 ≤ t.multiplier + 2 * (m : ℤ)
    change 0 ≤ t.multiplier + 2 * (n : ℤ) at hm
    omega
  · have h := ha v i
    change 0 ≤ t.exponent v i + (n : ℤ) ∧
      t.exponent v i + (n : ℤ) ≤ t.multiplier + 2 * (n : ℤ) at h
    change 0 ≤ t.exponent v i + (m : ℤ) ∧
      t.exponent v i + (m : ℤ) ≤ t.multiplier + 2 * (m : ℤ)
    constructor <;> omega

theorem Local.LocalType.exists_pair_integral_shift {s : ℕ} (u v : Local.LocalType s) :
    ∃ n : ℕ, (u.shift n).IsIntegral ∧ (v.shift n).IsIntegral := by
  obtain ⟨n, hn⟩ := u.exists_integral_shift
  obtain ⟨m, hm⟩ := v.exists_integral_shift
  exact ⟨n + m, u.shift_integral_mono hn (Nat.le_add_right _ _),
    v.shift_integral_mono hm (Nat.le_add_left _ _)⟩

theorem Local.LocalType.eq_of_shift_eq {s : ℕ} (u v : Local.LocalType s) (n : ℕ)
    (h : u.shift n = v.shift n) : u = v := by
  have hm : u.multiplier = v.multiplier := add_right_cancel
    (congrArg Local.LocalType.multiplier h)
  have ha : u.exponent = v.exponent := by
    funext i j
    exact add_right_cancel (congrArg (fun t : Local.LocalType s => t.exponent i j) h)
  cases u
  cases v
  dsimp at hm ha
  cases hm
  cases ha
  rfl

end

variable (s q : ℕ) [Fact q.Prime]

theorem IntegralTypeUniqueness.rawType_eq_of_common (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (u v : Local.LocalType s) (x : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q)
    (hu : x ∈ HeckeKernel.doubleCosetOrbit (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q u))
    (hv : x ∈ HeckeKernel.doubleCosetOrbit (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q v)) : u = v := by
  obtain ⟨n, hn, hm⟩ := u.exists_pair_integral_shift v
  let z := HeckeKernel.centralElement s q ^ n
  have hz (g : HeckeKernel.SplitGroup s q) : Commute g z := (HeckeKernel.centralElement_commutes s q g).pow_right n
  have hshift (t : Local.LocalType s)
      (ht : x ∈ HeckeKernel.doubleCosetOrbit (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q t)) :
      z⁻¹ • x ∈ HeckeKernel.doubleCosetOrbit (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q (t.shift n)) := by
    rw [CentralConvolution.representative_shift]
    apply (CentralConvolution.central_orbit_shift (HeckeKernel.integralLevel s q) z hz _ _).mp
    simpa only [smul_inv_smul] using ht
  have he := IntegralTypeUniqueness.rawIntegralType_eq_of_common s q hElementaryDivisors ⟨u.shift n, hn⟩ ⟨v.shift n, hm⟩
    (z⁻¹ • x) (hshift u hu) (hshift v hv)
  exact u.eq_of_shift_eq v n (congrArg Subtype.val he)

end AlgebraicGeometry.AbelianScheme.TateComparison

end

end OAI
