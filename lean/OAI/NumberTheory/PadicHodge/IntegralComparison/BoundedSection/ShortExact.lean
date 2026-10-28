import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Difference
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Short Exact -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.ShortExact

noncomputable section

/-!
# IntegralComparison: the short exact sequence governing compatible bounded sections
-/

open _root_.CategoryTheory Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustivePresheafSections OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveLinearSections OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Difference

universe u v w z t

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  [Preadditive D] (R : Type t) [CommRing R] [Linear R D]
  (P : ℕ → ObjectProperty C) (hP : Monotone P) (M : D) (F : Cᵒᵖ ⥤ D)

def sequence : ShortComplex (ModuleCat.{max u z} R) :=
  ShortComplex.mk (ModuleCat.ofHom (ExhaustiveLinearSections.compatibleSubmodule R P hP M F).subtype)
    (ModuleCat.ofHom (Difference.difference P hP M F R)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (Difference.compatible_iff_difference_zero P hP M F R x.val).mp x.property)

theorem exact_sequence : (sequence R P hP M F).Exact :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    ((Submodule.range_subtype (ExhaustiveLinearSections.compatibleSubmodule R P hP M F)).trans
      (Difference.compatibleSubmodule_eq_ker P hP M F R))

theorem shortExact
    (ht : ∀ n, Function.Surjective (ExhaustivePresheafSections.restrict P hP M F n (n + 1) (Nat.le_succ n))) :
    (sequence R P hP M F).ShortExact where
  exact := exact_sequence R P hP M F
  mono_f := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (SequentialModuleDifference.surjective R (fun n => ExhaustivePresheafSections.Stage P M F n)
      (fun n => ((Limit.diagram R P hP M F).map (homOfLE (Nat.le_succ n)).op).hom) ht)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.ShortExact
