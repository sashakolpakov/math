import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-! # Projective Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ProjectiveResolution

noncomputable section

/-! An exact augmented chain complex of projectives gives a projective
resolution with its specified, literal degree-zero augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : ChainComplex C ℕ) (Q : C) (ε : K.X 0 ⟶ Q) (w : K.d 1 0 ≫ ε = 0)

def augmentation : K ⟶ (ChainComplex.single₀ C).obj Q :=
  (ChainComplex.toSingle₀Equiv K Q).symm ⟨ε, w⟩

@[simp]
theorem augmentation_f_zero : (augmentation K Q ε w).f 0 = ε :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

variable (hK : ∀ n, K.ExactAt (n + 1)) (hε : (ShortComplex.mk (K.d 1 0) ε w).Exact) [Epi ε]

include hK hε in
theorem quasiIso : QuasiIso (augmentation K Q ε w) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨hε, inferInstance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by
          simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
          change ε = (augmentation K Q ε w).f 0
          exact (augmentation_f_zero K Q ε w).symm)
    · change K.d 0 0 = 0
      exact K.shape _ _ (by decide)
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact hK n
    · exact ChainComplex.exactAt_succ_single_obj Q n

variable [∀ n, Projective (K.X n)]

def resolution : ProjectiveResolution Q where
  complex := K
  projective n := inferInstanceAs (Projective (K.X n))
  π := augmentation K Q ε w
  quasiIso := Augmented.ProjectiveResolution.quasiIso K Q ε w hK hε

@[simp]
theorem resolution_π_f_zero : (resolution K Q ε w hK hε).π.f 0 = ε :=
  augmentation_f_zero K Q ε w

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ProjectiveResolution
