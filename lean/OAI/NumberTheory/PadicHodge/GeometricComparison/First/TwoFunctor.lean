import OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Two Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoFunctor.FirstTwoComplex

noncomputable section

/-! Functoriality and exactness of retaining only the first two cochain terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject

universe u v

section Additive

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

def functor : CochainComplex C ℕ ⥤ CochainComplex C ℕ where
  obj := TwoComplex.FirstTwoComplex.complex
  map := TwoComplex.FirstTwoComplex.map
  map_id K := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n => exact (isZero_zero C).eq_of_tgt _ _
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n => exact (isZero_zero C).eq_of_tgt _ _

instance additive : (functor C).Additive where
  map_add {K L} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n => exact (isZero_zero C).eq_of_tgt _ _

instance linear (R : Type*) [CommRing R] [Linear R C] : (functor C).Linear R where
  map_smul {K L} f r := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n => exact (isZero_zero C).eq_of_tgt _ _

end Additive

variable (C : Type u) [Category.{v} C] [Abelian C]

theorem shortExact (S : ShortComplex (CochainComplex C ℕ))
    (h : ∀ n : ℕ, n ≤ 1 → (S.map (HomologicalComplex.eval C (.up ℕ) n)).ShortExact) :
    (S.map (functor C)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  cases n with
  | zero => exact h 0 (by omega)
  | succ n =>
    cases n with
    | zero => exact h 1 (by omega)
    | succ n =>
      exact (ShortComplex.Splitting.ofIsZeroOfIsIso _ (isZero_zero C)
        ((isZero_zero C).isIso (isZero_zero C) _)).shortExact

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoFunctor.FirstTwoComplex
