import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Power Scalar Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PowerScalarLocalization

noncomputable section

/-!
# IntegralComparison: localization is preserved when scalars act through a positive-power endomorphism
-/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R] (σ : R →+* R) (q : ℕ)
  (hσ : ∀ r, σ r = r ^ q) (hq : 0 < q) (S : Submonoid R)
  {M N : ModuleCat.{v} R} (f : M ⟶ N) [IsLocalizedModule S f.hom]

include hσ hq in
theorem isLocalizedModule : IsLocalizedModule S ((ModuleCat.restrictScalars σ).map f).hom := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  constructor
  · intro s
    rw [Module.End.isUnit_iff]
    change Function.Bijective (fun x : N => σ (s : R) • x)
    rw [hσ]
    exact (Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units f.hom (⟨(s : R) ^ (m + 1), S.pow_mem s.2 _⟩ : S))
  · intro y
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S f.hom (show N from y)
    refine ⟨⟨(s : R) ^ m • x, s⟩, ?_⟩
    change σ (s : R) • (show N from y) = f.hom ((s : R) ^ m • x)
    rw [hσ, pow_succ, mul_smul, show (s : R) • (show N from y) = f.hom x from hs,
      f.hom.map_smul]
  · intro x y h
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f.hom) h
    refine ⟨s, ?_⟩
    change σ (s : R) • (show M from x) = σ (s : R) • (show M from y)
    rw [hσ, pow_succ, mul_smul, mul_smul]
    exact congrArg (fun z : M => (s : R) ^ m • z) hs

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PowerScalarLocalization
