import Mathlib.Algebra.Homology.Augment
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Resolution Augment -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ResolutionAugment

noncomputable section

/-! Attach a projective middle term to a resolution of the kernel in a
short exact sequence. This constructs the next bounded resolution without
assuming a derived-functor vanishing theorem. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex C) (hS : S.ShortExact)
  (Q : ProjectiveResolution S.X₁)

def complex : ChainComplex C ℕ :=
  Q.complex.augment (Q.π.f 0 ≫ S.f) (by rw [← Category.assoc, Q.complex_d_comp_π_f_zero, zero_comp])

include hS in
theorem complex_exact_zero :
    (ShortComplex.mk ((ResolutionAugment.complex S Q).d 1 0) S.g (by simp [ResolutionAugment.complex])).Exact := by
  let T := ShortComplex.mk ((ResolutionAugment.complex S Q).d 1 0) S.g (by simp [ResolutionAugment.complex])
  let φ : T ⟶ S :=
    { τ₁ := Q.π.f 0, τ₂ := 𝟙 _, τ₃ := 𝟙 _
      comm₁₂ := by simp [T, ResolutionAugment.complex]
      comm₂₃ := by simp [T, ResolutionAugment.complex] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hS.exact

include hS in
theorem complex_exact_succ (n : ℕ) : (ResolutionAugment.complex S Q).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  cases n with
  | zero =>
    let T := ShortComplex.mk (Q.complex.d 1 0) (Q.π.f 0) Q.complex_d_comp_π_f_zero
    let U := (ResolutionAugment.complex S Q).sc' 2 1 0
    let φ : T ⟶ U :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := S.f
        comm₁₂ := by simp [T, U, ResolutionAugment.complex]
        comm₂₃ := by simp [T, U, ResolutionAugment.complex] }
    let : Mono S.f := hS.mono_f
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp Q.exact₀
  | succ n =>
    simpa only [ResolutionAugment.complex, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
      ChainComplex.augment_d_succ_succ] using Q.exact_succ n

variable [Projective S.X₂]

def resolution : ProjectiveResolution S.X₃ where
  complex := ResolutionAugment.complex S Q
  projective n := by
    cases n with
    | zero => exact inferInstanceAs (Projective S.X₂)
    | succ n => exact Q.projective n
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨S.g, by simp [ResolutionAugment.complex]⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).mpr
          ⟨complex_exact_zero S hS Q, hS.epi_g⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [ResolutionAugment.complex]) (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exact_succ S hS Q n
      · exact ChainComplex.exactAt_succ_single_obj _ n⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ResolutionAugment
