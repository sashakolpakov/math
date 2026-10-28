import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.GradedModule

/-! # Fractions -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.Fractions.GradedModules

noncomputable section

/-! Linear numerator maps and denominator clearing in actual module localizations. -/

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

def moduleDenominator (a : A) (k : ℕ) : Submonoid.powers a := ⟨a ^ k, k, rfl⟩

abbrev AwayModule (a : A) (M : Type w) [AddCommGroup M] [Module A M] :=
  LocalizedModule (Submonoid.powers a) M

def moduleFractionMap (a : A) (k : ℕ) : M →ₗ[R] AwayModule a M :=
  ((LocalizedModule.divBy (moduleDenominator a k)).comp
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)).restrictScalars R

theorem moduleFractionMap_apply (a : A) (k : ℕ) (m : M) :
    moduleFractionMap (R := R) a k m = LocalizedModule.mk m (moduleDenominator a k) := by
  simp only [moduleFractionMap, LinearMap.restrictScalars_apply, LinearMap.comp_apply,
    LocalizedModule.mkLinearMap_apply, LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]

theorem moduleDenominator_add (a : A) (k l : ℕ) :
    moduleDenominator a (k + l) = moduleDenominator a k * moduleDenominator a l := by
  apply Subtype.ext
  exact pow_add a k l

theorem moduleFractionMap_raise (a : A) (k l : ℕ) (m : M) :
    moduleFractionMap (R := R) a (k + l) (a ^ l • m) = moduleFractionMap (R := R) a k m := by
  rw [moduleFractionMap_apply, moduleFractionMap_apply, moduleDenominator_add]
  exact LocalizedModule.mk_cancel_common_right (moduleDenominator a k) (moduleDenominator a l) m

theorem moduleFractionMap_surj (a : A) (x : AwayModule a M) :
    ∃ (k : ℕ) (m : M), moduleFractionMap (R := R) a k m = x := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨k, hk⟩ := s.property
    refine ⟨k, m, ?_⟩
    rw [moduleFractionMap_apply]
    congr 1
    exact Subtype.ext hk

theorem moduleFractionMap_eq_zero (a : A) (k : ℕ) (m : M) :
    moduleFractionMap (R := R) a k m = 0 ↔ ∃ l : ℕ, a ^ l • m = 0 := by
  rw [moduleFractionMap_apply, ← LocalizedModule.zero_mk (moduleDenominator a 0),
    LocalizedModule.mk_eq]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨l, hl⟩ := s.property
    refine ⟨l, ?_⟩
    simpa only [Submonoid.smul_def, moduleDenominator, pow_zero, one_smul, smul_zero, ← hl] using hs
  · rintro ⟨l, hl⟩
    refine ⟨moduleDenominator a l, ?_⟩
    simpa only [Submonoid.smul_def, moduleDenominator, pow_zero, one_smul, smul_zero] using hl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.Fractions.GradedModules
