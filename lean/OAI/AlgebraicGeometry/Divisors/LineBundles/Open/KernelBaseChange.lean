import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Kernel Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.KernelBaseChange.BundleCycles

noncomputable section

/-! # LineBundleCycles: scheme-theoretic image ideals commute with actual open base change -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem openKernel_comap_of_isPullback {A B X Y : Scheme.{0}} (f : A ⟶ Y) (g : B ⟶ X)
    (j : B ⟶ A) (i : X ⟶ Y) [IsOpenImmersion i] [QuasiCompact f]
    (h : IsPullback g j i f) : f.ker.comap i = g.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f g j i h U).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.KernelBaseChange.BundleCycles
