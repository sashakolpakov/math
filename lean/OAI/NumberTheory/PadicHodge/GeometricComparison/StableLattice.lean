import OAI.NumberTheory.PadicHodge.GeometricComparison.LatticeBound
import OAI.NumberTheory.PadicHodge.GeometricComparison.FiltrationBounds

/-! # Stable Lattice -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.StableLattice.StableLatticeAdmissibility

noncomputable section

/-! Frobenius divisibility on a full integral Hodge lattice gives every stable-subspace inequality. -/

open scoped nonZeroDivisors

variable (p : ℕ) [Fact p.Prime]
  {M V : Type*} [AddCommGroup M] [Module ℤ_[p] M]
  [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M]
  [AddCommGroup V] [Module ℤ_[p] V] [Module ℚ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
  [FiniteDimensional ℚ_[p] V]
  (f : M →ₗ[ℤ_[p]] V) [IsLocalizedModule ℤ_[p]⁰ f]
  (F : Module.End ℤ_[p] M) (φ : V ≃ₗ[ℚ_[p]] V)
  (hcomm : ∀ x, f (F x) = φ (f x))

include hcomm

theorem subspace_inequality (H : Submodule ℚ_[p] V)
    (hdiv : ∀ x, f x ∈ H → ∃ y, F x = (p : ℤ_[p]) • y)
    (S : Submodule ℚ_[p] V) (hS : S ≤ S.comap φ.toLinearMap) :
    (Module.finrank ℚ_[p] (H.comap S.subtype) : ℤ) ≤
      Padic.valuation (φ.toLinearMap.restrict hS).det := by
  let P := LatticeSubspaceEq.LatticeSubspace.integralPart f S
  let g := LatticeSubspaceEq.LatticeSubspace.inclusion f S
  have hP : P ≤ P.comap F := by
    intro x hx
    change f (F x) ∈ S
    rw [hcomm]
    exact hS hx
  let G := (F.domRestrict P).codRestrict P (fun x => hP x.property)
  let ψ := φ.toLinearMap.restrict hS
  have hψ : ψ.det ≠ 0 := by
    intro hz
    have hk : ψ.ker = ⊥ := LinearMap.ker_eq_bot.mpr (by
      intro x y hxy
      exact Subtype.ext (φ.injective (congrArg Subtype.val hxy)))
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) hk
  apply LatticeBound.LatticeHodgeBound.inequality p g G ψ hψ
  · intro x
    exact Subtype.ext (hcomm x)
  · intro x hx
    obtain ⟨y, hy⟩ := hdiv x hx
    have hpy : (p : ℚ_[p]) • f y ∈ S := by
      have h := hP x.property
      change f (F x) ∈ S at h
      rw [hy, map_smul] at h
      rwa [← IsScalarTower.algebraMap_smul ℚ_[p] (p : ℤ_[p]) (f y), map_natCast] at h
    have hyS : y ∈ P :=
      (S.smul_mem_iff (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)).mp hpy
    exact ⟨⟨y, hyS⟩, Subtype.ext hy⟩

theorem weaklyAdmissible (Fil : Linear.FiniteFiltration ℚ_[p] V)
    (h0 : Fil.step 0 = ⊤) (h2 : Fil.step 2 = ⊥)
    (htotal : Fil.tH = (Padic.valuation φ.toLinearMap.det : ℚ))
    (hdiv : ∀ x, f x ∈ Fil.step 1 → ∃ y, F x = (p : ℤ_[p]) • y) :
    Linear.WeaklyAdmissible p Fil φ := by
  refine ⟨htotal, fun S hS => ?_⟩
  rw [FirstHodgeNumber.FiltrationTransport.tH_h1 (Fil.restrict S)
    (FiltrationBounds.FiltrationTransport.restrict_top Fil S 0 h0)
    (FiltrationBounds.FiltrationTransport.restrict_bot Fil S 2 h2)]
  exact_mod_cast subspace_inequality p f F φ hcomm (Fil.step 1) hdiv S hS

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.StableLattice.StableLatticeAdmissibility
