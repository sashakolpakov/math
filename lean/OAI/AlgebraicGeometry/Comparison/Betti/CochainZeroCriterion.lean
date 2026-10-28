import OAI.AlgebraicGeometry.Comparison.Betti.Module.HomologyClasses
import Mathlib.Algebra.Homology.QuasiIso

/-! # Cochain Zero Criterion -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CochainZeroCriterion.Homology

noncomputable section

/-! A concrete closed-section criterion for degree-zero comparison of module cochains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

variable {R : Type} [Ring R]

theorem short_quasiIso_of_closed_lift {S T : ShortComplex (ModuleCat.{0} R)}
    (f : S ⟶ T) (hS : S.f = 0) (hT : T.f = 0)
    (hi : Function.Injective f.τ₂)
    (hs : ∀ y : T.X₂, T.g y = 0 → ∃ x : S.X₂, S.g x = 0 ∧ f.τ₂ x = y) :
    ShortComplex.QuasiIso f := by
  have hm : Mono f.τ₂ := (ModuleCat.mono_iff_injective _).mpr hi
  have hsurj : Function.Surjective (ShortComplex.cyclesMap f) := by
    intro y
    have hy : T.g (T.iCycles y) = 0 := ConcreteCategory.congr_hom T.iCycles_g y
    obtain ⟨x, hx, he⟩ := hs (T.iCycles y) hy
    let z := Module.HomologyClasses.cycle S x hx
    refine ⟨z, ?_⟩
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    have hn := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i f) z
    change T.iCycles (ShortComplex.cyclesMap f z) = T.iCycles y
    rw [show T.iCycles (ShortComplex.cyclesMap f z) = f.τ₂ (S.iCycles z) from hn]
    rw [Module.HomologyClasses.cycle_i]
    exact he
  have hmono : Mono (ShortComplex.cyclesMap f) :=
    mono_of_mono_fac (ShortComplex.cyclesMap_i f)
  have hc : IsIso (ShortComplex.cyclesMap f) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(ModuleCat.mono_iff_injective _).mp inferInstance, hsurj⟩
  have hpS := S.isIso_homologyπ hS
  have hpT := T.isIso_homologyπ hT
  rw [ShortComplex.quasiIso_iff]
  have he : ShortComplex.homologyMap f =
      inv S.homologyπ ≫ ShortComplex.cyclesMap f ≫ T.homologyπ := by
    rw [← cancel_epi S.homologyπ]
    simp only [IsIso.hom_inv_id_assoc, ShortComplex.homologyπ_naturality]
  rw [he]
  infer_instance

theorem quasiIsoAt_zero_of_closed_lift {K L : CochainComplex (ModuleCat.{0} R) ℕ}
    (f : K ⟶ L) (hi : Function.Injective (f.f 0))
    (hs : ∀ y : L.X 0, L.d 0 1 y = 0 →
      ∃ x : K.X 0, K.d 0 1 x = 0 ∧ f.f 0 x = y) : QuasiIsoAt f 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  exact short_quasiIso_of_closed_lift _ (K.shape 0 0 (by simp)) (L.shape 0 0 (by simp)) hi hs

end

end OAI.AlgebraicGeometry.Comparison.Betti.CochainZeroCriterion.Homology
