import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.AlgebraicGeometry.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Represented Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedRelations

noncomputable section

/-! A represented relation whose functor of points is an equivalence
relation has actual identity, symmetry, and composition morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {C : Type*} [Category C] {R X : C} (s t : R ⟶ X)

def homRelation {T : C} (a b : T ⟶ X) : Prop :=
  ∃ f : T ⟶ R, f ≫ s = a ∧ f ≫ t = b

theorem exists_equivalenceRelation_of_hom [HasPullback t s] [JointlyMono₂ s t]
    (he : ∀ T : C, Equivalence (homRelation s t (T := T))) :
    Nonempty (CategoryTheory.EquivalenceRelation s t) := by
  obtain ⟨r, hrs, hrt⟩ := (he X).refl (𝟙 X)
  obtain ⟨u, hus, hut⟩ := (he R).symm
    (show homRelation s t s t from ⟨𝟙 R, Category.id_comp _, Category.id_comp _⟩)
  have hpair : homRelation s t (pullback.fst t s ≫ s) (pullback.snd t s ≫ t) :=
    (he (pullback t s)).trans
      ⟨pullback.fst t s, rfl, pullback.condition⟩
      ⟨pullback.snd t s, rfl, rfl⟩
  obtain ⟨v, hvs, hvt⟩ := hpair
  exact ⟨{
    r := r
    reflexivity₁ := hrs
    reflexivity₂ := hrt
    s := u
    symmetry₁ := hus
    symmetry₂ := hut
    c := pullback.cone t s
    isLimit := pullback.isLimit t s
    t := v
    transitivity₁ := hvs
    transitivity₂ := hvt }⟩

theorem over_jointlyMono_left {S : Scheme.{0}} {R X : Over S} (s t : R ⟶ X)
    [JointlyMono₂ s t] : JointlyMono₂ s.left t.left where
  right_cancellation {Y} f g hs ht := by
    let T : Over S := Over.mk (f ≫ R.hom)
    let f' : T ⟶ R := Over.homMk f rfl
    have hg : g ≫ R.hom = f ≫ R.hom := by
      rw [← s.w, ← Category.assoc, ← Category.assoc, hs]
    let g' : T ⟶ R := Over.homMk g hg
    have h : f' = g' := JointlyMono₂.right_cancellation (p₁ := s) (p₂ := t) f' g'
      (Over.OverMorphism.ext hs) (Over.OverMorphism.ext ht)
    exact congrArg (fun h : T ⟶ R => h.left) h

def over_equivalenceRelation_left {S : Scheme.{0}} {R X : Over S} {s t : R ⟶ X}
    (e : CategoryTheory.EquivalenceRelation s t) : CategoryTheory.EquivalenceRelation s.left t.left := by
  let : JointlyMono₂ s t := e.toJointlyMono₂
  let : JointlyMono₂ ((Over.forget S).map s) ((Over.forget S).map t) := over_jointlyMono_left s t
  let hsym := e.toSymmetricRelation.map (Over.forget S)
  let htrans := e.toTransitiveRelation.map (Over.forget S)
  exact {
    toReflexiveRelation := e.toReflexiveRelation.map (Over.forget S)
    s := hsym.s
    symmetry₁ := hsym.symmetry₁
    symmetry₂ := hsym.symmetry₂
    c := htrans.c
    isLimit := htrans.isLimit
    t := htrans.t
    transitivity₁ := htrans.transitivity₁
    transitivity₂ := htrans.transitivity₂ }

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedRelations
