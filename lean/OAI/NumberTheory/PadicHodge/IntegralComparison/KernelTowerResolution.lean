import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Basic

/-! # Kernel Tower Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerResolution

noncomputable section

/-! Successive epimorphisms onto kernels give an actual augmented chain
resolution. No projectivity of the chosen terms is required. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

structure Tower where
  object : ℕ → C
  term : ℕ → C
  projection : ∀ n, term n ⟶ object n
  epi : ∀ n, Epi (projection n)
  kernelIso : ∀ n, object (n + 1) ≅ kernel (projection n)

namespace Tower

variable (T : Tower (C := C))

instance (n : ℕ) : Epi (T.projection n) := T.epi n

def inclusion (n : ℕ) : T.object (n + 1) ⟶ T.term n :=
  (T.kernelIso n).hom ≫ kernel.ι (T.projection n)

instance (n : ℕ) : Mono (T.inclusion n) := by
  dsimp only [Tower.inclusion]
  infer_instance

@[reassoc (attr := simp)]
theorem inclusion_projection (n : ℕ) : T.inclusion n ≫ T.projection n = 0 := by
  simp [Tower.inclusion]

def sequence (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (T.inclusion n) (T.projection n) (T.inclusion_projection n)

theorem sequence_shortExact (n : ℕ) : (T.sequence n).ShortExact := by
  have : Mono (T.sequence n).f := inferInstanceAs (Mono (T.inclusion n))
  have : Epi (T.sequence n).g := T.epi n
  apply ShortComplex.ShortExact.mk
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  have h : kernel.lift (T.projection n) (T.inclusion n) (T.inclusion_projection n) =
      (T.kernelIso n).hom := by
    apply (cancel_mono (kernel.ι (T.projection n))).mp
    simp [Tower.inclusion]
  change Epi (kernel.lift (T.projection n) (T.inclusion n) (T.inclusion_projection n))
  rw [h]
  infer_instance

def differential (n : ℕ) : T.term (n + 1) ⟶ T.term n :=
  T.projection (n + 1) ≫ T.inclusion n

@[reassoc (attr := simp)]
theorem differential_projection (n : ℕ) : T.differential n ≫ T.projection n = 0 := by
  simp [Tower.differential]

theorem differential_squared (n : ℕ) : T.differential (n + 1) ≫ T.differential n = 0 := by
  simp [Tower.differential, Category.assoc]

theorem exact_projection (n : ℕ) :
    (ShortComplex.mk (T.differential n) (T.projection n) (T.differential_projection n)).Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  have h : kernel.lift (T.projection n) (T.differential n) (T.differential_projection n) =
      T.projection (n + 1) ≫ (T.kernelIso n).hom := by
    apply (cancel_mono (kernel.ι (T.projection n))).mp
    simp [Tower.differential, Tower.inclusion]
  rw [h]
  infer_instance

theorem exact_differential (n : ℕ) :
    (ShortComplex.mk (T.differential (n + 1)) (T.differential n) (T.differential_squared n)).Exact := by
  let S := ShortComplex.mk (T.differential (n + 1)) (T.projection (n + 1))
    (T.differential_projection (n + 1))
  let U := ShortComplex.mk (T.differential (n + 1)) (T.differential n) (T.differential_squared n)
  let φ : S ⟶ U :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := T.inclusion n
      comm₁₂ := by simp [S, U]
      comm₂₃ := by simp [S, U, Tower.differential] }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 (T.term (n + 2))))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (T.term (n + 1))))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (T.inclusion n))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp (T.exact_projection (n + 1))

def complex : ChainComplex C ℕ :=
  ChainComplex.of T.term T.differential T.differential_squared

@[simp]
theorem complex_d (n : ℕ) : (T.complex).d (n + 1) n = T.differential n :=
  ChainComplex.of_d T.term T.differential n

theorem exactAt_succ (n : ℕ) : T.complex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', Tower.complex,
    ChainComplex.of_d] using
    T.exact_differential n

def augmentation : T.complex ⟶ (ChainComplex.single₀ C).obj (T.object 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨T.projection 0, by rw [T.complex_d]; exact T.differential_projection 0⟩

@[simp]
theorem augmentation_zero : T.augmentation.f 0 = T.projection 0 :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

set_option backward.isDefEq.respectTransparency false in
instance : QuasiIso T.augmentation := ⟨fun n => by
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
        ⟨T.exact_projection 0, inferInstance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp)
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact T.exactAt_succ n
    · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end Tower

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerResolution
