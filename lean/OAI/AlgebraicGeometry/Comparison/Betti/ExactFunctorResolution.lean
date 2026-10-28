import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionExactImage
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Exact Functor Resolution -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ExactFunctorResolution

noncomputable section

/-! Exact functors retain the actual augmentation of a proved resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (T : C ⥤ D) [T.Additive] [T.PreservesHomology] [T.PreservesMonomorphisms]
  {Z : C} (R : ResolutionExactImage.Data Z)

def mapResolutionData : ResolutionExactImage.Data (T.obj Z) where
  complex := (T.mapHomologicalComplex (.up ℕ)).obj R.complex
  augmentation := T.map R.augmentation
  augmentation_d := by
    change T.map R.augmentation ≫ T.map (R.complex.d 0 1) = 0
    rw [← T.map_comp, R.augmentation_d, T.map_zero]
  isKernel := by
    have hm : Mono (T.map R.augmentation) := T.map_mono R.augmentation
    let S := ShortComplex.mk R.augmentation (R.complex.d 0 1) R.augmentation_d
    have hm' : Mono (S.map T).f := hm
    have he : (S.map T).Exact := (ShortComplex.exact_of_f_is_kernel S R.isKernel).map T
    exact he.fIsKernel
  exact_succ n := by
    have he := (R.complex.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).mp (R.exact_succ n)
    exact (((T.mapHomologicalComplex (.up ℕ)).obj R.complex).exactAt_iff'
      n (n + 1) (n + 2) (by simp) (by simp)).mpr (he.map T)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ExactFunctorResolution
