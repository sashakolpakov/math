import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Cochain Classes -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses

noncomputable section

/-! Concrete cycle classes in the original homology of a module cochain complex. -/

open _root_.CategoryTheory Limits

universe u v

variable {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{v} R) ℕ)

abbrev cycles (n : ℕ) : Submodule R (K.X n) := (K.d n (n + 1)).hom.ker

abbrev short (n : ℕ) := K.sc' ((ComplexShape.up ℕ).prev n) n (n + 1)

def boundaries (n : ℕ) : Submodule R (cycles K n) :=
  (short K n).moduleCatToCycles.range

def quotientIso (n : ℕ) : K.homology n ≅ ModuleCat.of R (cycles K n ⧸ boundaries K n) :=
  K.homologyIsoSc' _ n (n + 1) rfl (CochainComplex.next ℕ n) ≪≫
    (short K n).moduleCatHomologyIso

def classMap (n : ℕ) : cycles K n →ₗ[R] K.homology n :=
  (quotientIso K n).inv.hom.comp (boundaries K n).mkQ

theorem classMap_surjective (n : ℕ) : Function.Surjective (classMap K n) :=
  (ModuleCat.epi_iff_surjective (quotientIso K n).inv).mp inferInstance |>.comp
    (Submodule.mkQ_surjective (boundaries K n))

theorem classMap_eq_zero_iff (n : ℕ) (x : cycles K n) :
    classMap K n x = 0 ↔ ∃ y : K.X ((ComplexShape.up ℕ).prev n),
      K.d ((ComplexShape.up ℕ).prev n) n y = x.val := by
  have h0 : classMap K n x = 0 ↔ (boundaries K n).mkQ x = 0 := by
    constructor
    · intro h
      apply (ModuleCat.mono_iff_injective (quotientIso K n).inv).mp inferInstance
      exact h.trans (quotientIso K n).inv.hom.map_zero.symm
    · intro h
      change (quotientIso K n).inv.hom ((boundaries K n).mkQ x) = 0
      rw [h, map_zero]
  rw [h0]
  change Submodule.Quotient.mk x = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

theorem classMap_succ_eq_zero_iff (n : ℕ) (x : cycles K (n + 1)) :
    classMap K (n + 1) x = 0 ↔ ∃ y : K.X n, K.d n (n + 1) y = x.val := by
  have hprev : (ComplexShape.up ℕ).prev (n + 1) = n := (ComplexShape.up ℕ).prev_eq' rfl
  have h := classMap_eq_zero_iff K (n + 1) x
  rwa [hprev] at h

theorem classMap_zero_eq_zero_iff (x : cycles K 0) :
    classMap K 0 x = 0 ↔ x = 0 := by
  rw [classMap_eq_zero_iff]
  have hprev : (ComplexShape.up ℕ).prev 0 = 0 := CochainComplex.prev_nat_zero
  rw [hprev]
  rw [K.shape 0 0 (by simp)]
  change (∃ _ : K.X 0, (0 : K.X 0) = x.val) ↔ x = 0
  constructor
  · rintro ⟨_, h⟩
    exact Subtype.ext h.symm
  · rintro rfl
    exact ⟨0, rfl⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses
