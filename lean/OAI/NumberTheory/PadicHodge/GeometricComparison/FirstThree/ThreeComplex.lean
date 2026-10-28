import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.Linear

/-! # Three Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex

noncomputable section

/-! The native quotient complex retaining degrees zero, one and two. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

def term (K : CochainComplex C ℕ) : ℕ → C
  | 0 => K.X 0
  | 1 => K.X 1
  | 2 => K.X 2
  | _ + 3 => 0

def differential (K : CochainComplex C ℕ) : ∀ n, term K n ⟶ term K (n + 1)
  | 0 => K.d 0 1
  | 1 => K.d 1 2
  | _ + 2 => 0

def complex (K : CochainComplex C ℕ) : CochainComplex C ℕ :=
  CochainComplex.of (term K) (differential K) (by
    intro n
    rcases n with _ | (_ | n)
    · exact K.d_comp_d 0 1 2
    · exact comp_zero
    · exact zero_comp)

def projectionTerm (K : CochainComplex C ℕ) : ∀ n, K.X n ⟶ term K n
  | 0 => 𝟙 _
  | 1 => 𝟙 _
  | 2 => 𝟙 _
  | _ + 3 => 0

def projection (K : CochainComplex C ℕ) : K ⟶ complex K where
  f n := projectionTerm K n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    rw [show (complex K).d n (n + 1) = differential K n from CochainComplex.of_d _ _ n]
    rcases n with _ | (_ | n)
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact (isZero_zero C).eq_of_tgt _ _

def mapTerm {K L : CochainComplex C ℕ} (f : K ⟶ L) : ∀ n, term K n ⟶ term L n
  | 0 => f.f 0
  | 1 => f.f 1
  | 2 => f.f 2
  | _ + 3 => 0

def map {K L : CochainComplex C ℕ} (f : K ⟶ L) : complex K ⟶ complex L where
  f n := mapTerm f n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    rw [show (complex K).d n (n + 1) = differential K n from CochainComplex.of_d _ _ n,
      show (complex L).d n (n + 1) = differential L n from CochainComplex.of_d _ _ n]
    rcases n with _ | (_ | n)
    · exact f.comm 0 1
    · exact f.comm 1 2
    · exact (isZero_zero C).eq_of_tgt _ _

theorem projection_naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    projection K ≫ FirstThreeComplex.map f = f ≫ projection L := by
  apply HomologicalComplex.Hom.ext
  funext n
  rcases n with _ | (_ | (_ | n))
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact zero_comp.trans comp_zero.symm

def functor (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C] :
    CochainComplex C ℕ ⥤ CochainComplex C ℕ where
  obj := complex
  map := FirstThreeComplex.map
  map_id K := by
    apply HomologicalComplex.Hom.ext
    funext n
    rcases n with _ | (_ | (_ | n))
    · rfl
    · rfl
    · rfl
    · exact (isZero_zero C).eq_of_tgt _ _
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    rcases n with _ | (_ | (_ | n))
    · rfl
    · rfl
    · rfl
    · exact (isZero_zero C).eq_of_tgt _ _

instance additive : (functor C).Additive where
  map_add {K L} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    rcases n with _ | (_ | (_ | n))
    · rfl
    · rfl
    · rfl
    · exact (isZero_zero C).eq_of_tgt _ _

instance linear (R : Type*) [CommRing R] [Linear R C] : (functor C).Linear R where
  map_smul {K L} f r := by
    apply HomologicalComplex.Hom.ext
    funext n
    rcases n with _ | (_ | (_ | n))
    · rfl
    · rfl
    · rfl
    · exact (isZero_zero C).eq_of_tgt _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex
