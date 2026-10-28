import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.Linear

/-! # Two Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoComplex.FirstTwoComplex

noncomputable section

/-! The quotient of a nonnegative cochain complex retaining only its first two terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

def term (K : CochainComplex C ℕ) : ℕ → C
  | 0 => K.X 0
  | 1 => K.X 1
  | _ + 2 => 0

def differential (K : CochainComplex C ℕ) : ∀ n, term K n ⟶ term K (n + 1)
  | 0 => K.d 0 1
  | _ + 1 => 0

def complex (K : CochainComplex C ℕ) : CochainComplex C ℕ :=
  CochainComplex.of (term K) (differential K) (by
    intro n
    cases n with
    | zero => exact comp_zero
    | succ n => exact zero_comp)

def projectionTerm (K : CochainComplex C ℕ) : ∀ n, K.X n ⟶ term K n
  | 0 => 𝟙 _
  | 1 => 𝟙 _
  | _ + 2 => 0

def projection (K : CochainComplex C ℕ) : K ⟶ complex K where
  f n := projectionTerm K n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    rw [show (complex K).d n (n + 1) = differential K n from CochainComplex.of_d _ _ n]
    cases n with
    | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | succ n => exact (isZero_zero C).eq_of_tgt _ _

def mapTerm {K L : CochainComplex C ℕ} (f : K ⟶ L) : ∀ n, term K n ⟶ term L n
  | 0 => f.f 0
  | 1 => f.f 1
  | _ + 2 => 0

def map {K L : CochainComplex C ℕ} (f : K ⟶ L) : complex K ⟶ complex L where
  f n := mapTerm f n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    rw [show (complex K).d n (n + 1) = differential K n from CochainComplex.of_d _ _ n,
      show (complex L).d n (n + 1) = differential L n from CochainComplex.of_d _ _ n]
    cases n with
    | zero => exact f.comm 0 1
    | succ n => exact (isZero_zero C).eq_of_tgt _ _

theorem projection_naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    projection K ≫ map f = f ≫ projection L := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ n =>
    cases n with
    | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | succ n => exact zero_comp.trans comp_zero.symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoComplex.FirstTwoComplex
