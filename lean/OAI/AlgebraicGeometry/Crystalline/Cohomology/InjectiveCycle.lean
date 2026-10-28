import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Injective Cycle -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower

noncomputable section

/-!
# Short exact sequences of cycles in an injective resolution

The kernels of successive differentials form a tower of short exact
sequences with the original injective terms in the middle. Degree-zero
cycles are canonically isomorphic to the resolved object. All objects
and maps are taken from the given injective resolution.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] {F : C} (I : InjectiveResolution F)

def cycle (n : ℕ) : C := kernel (I.cocomplex.d n (n + 1))

def inclusion (n : ℕ) : cycle I n ⟶ I.cocomplex.X n := kernel.ι _

def projection (n : ℕ) : I.cocomplex.X n ⟶ cycle I (n + 1) :=
  kernel.lift (I.cocomplex.d (n + 1) (n + 2)) (I.cocomplex.d n (n + 1)) (I.complex_d_comp n)

theorem projection_inclusion (n : ℕ) :
    projection I n ≫ inclusion I (n + 1) = I.cocomplex.d n (n + 1) :=
  kernel.lift_ι _ _ _

theorem inclusion_projection (n : ℕ) : inclusion I n ≫ projection I n = 0 := by
  have : Mono (inclusion I (n + 1)) := by change Mono (kernel.ι _); infer_instance
  apply (cancel_mono (inclusion I (n + 1))).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => inclusion I n ≫ f) (projection_inclusion I n)).trans
      ((kernel.condition (I.cocomplex.d n (n + 1))).trans
        (zero_comp : (0 : cycle I n ⟶ cycle I (n + 1)) ≫ inclusion I (n + 1) = 0).symm))

def shortComplex (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (inclusion I n) (projection I n) (inclusion_projection I n)

def comparison (n : ℕ) : shortComplex I n ⟶
    ShortComplex.mk (kernel.ι (I.cocomplex.d n (n + 1))) (I.cocomplex.d n (n + 1)) (kernel.condition _) :=
  ShortComplex.Hom.mk (𝟙 _) (𝟙 _) (inclusion I (n + 1))
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (projection_inclusion I n).symm)

theorem shortExact (n : ℕ) : (shortComplex I n).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · have : Epi (comparison I n).τ₁ := by change Epi (𝟙 (cycle I n)); infer_instance
    have : IsIso (comparison I n).τ₂ := by change IsIso (𝟙 (I.cocomplex.X n)); infer_instance
    have : Mono (comparison I n).τ₃ := by change Mono (kernel.ι _); infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (comparison I n)).mpr
      (ShortComplex.kernelSequence_exact (I.cocomplex.d n (n + 1)))
  · change Mono (kernel.ι (I.cocomplex.d n (n + 1)))
    infer_instance
  · have hI : (I.cocomplex.sc' n (n + 1) (n + 2)).Exact :=
      (I.cocomplex.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).mp (I.cocomplex_exactAt_succ n)
    exact ((I.cocomplex.sc' n (n + 1) (n + 2)).exact_iff_epi_kernel_lift).mp hI

instance middle_injective (n : ℕ) : Injective (shortComplex I n).X₂ := by
  change Injective (I.cocomplex.X n)
  infer_instance

def augmentationIso : F ≅ cycle I 0 :=
  I.isLimitKernelFork.conePointUniqueUpToIso (limit.isLimit (parallelPair (I.cocomplex.d 0 1) 0))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower
