import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Words

/-! # Word Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.WordBaseChange.DifferenceWords

noncomputable section

/-! Canonical base-change and isomorphism compatibility of finite words. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {B C : Scheme.{u}}

def domainMap {X Y : Over B} (f : X ⟶ Y) : (n : ℕ) → Words.DifferenceWords.domain X n ⟶ Words.DifferenceWords.domain Y n
  | 0 => 𝟙 _
  | n + 1 => domainMap f n ⊗ₘ (f ⊗ₘ f)

def domainIso {X Y : Over B} (e : X ≅ Y) : (n : ℕ) → Words.DifferenceWords.domain X n ≅ Words.DifferenceWords.domain Y n
  | 0 => Iso.refl _
  | n + 1 => tensorIso (domainIso e n) (tensorIso e e)

@[simp] theorem domainIso_hom {X Y : Over B} (e : X ≅ Y) (n : ℕ) :
    (DifferenceWords.domainIso e n).hom = DifferenceWords.domainMap e.hom n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [DifferenceWords.domainIso, DifferenceWords.domainMap, ih]

theorem map_naturality {X Y A H : Over B} [GrpObj A] [GrpObj H]
    (a : X ⟶ A) (b : Y ⟶ H) (f : X ⟶ Y) (h : A ⟶ H) [IsMonHom h]
    (ha : a ≫ h = f ≫ b) (n : ℕ) :
    Words.DifferenceWords.map a n ≫ h = DifferenceWords.domainMap f n ≫ Words.DifferenceWords.map b n := by
  induction n with
  | zero => simp [Words.DifferenceWords.map, DifferenceWords.domainMap]
  | succ n ih =>
    simp only [Words.DifferenceWords.map, MonObj.mul_comp, MonObj.comp_mul, Category.assoc, ih]
    simp [DifferenceWords.domainMap, Words.DifferenceWords.difference, GrpObj.div_comp, GrpObj.comp_div,
      Category.assoc, ha]

/-- Base change of the iterated word domain is its iterated fiber product. -/
def baseChangeDomain (g : C ⟶ B) (X : Over B) : (n : ℕ) →
    (Over.pullback g).obj (Words.DifferenceWords.domain X n) ≅ Words.DifferenceWords.domain ((Over.pullback g).obj X) n
  | 0 => (Functor.Monoidal.εIso (Over.pullback g)).symm
  | n + 1 =>
      asIso (prodComparison (Over.pullback g) (Words.DifferenceWords.domain X n) (X ⊗ X)) ≪≫
        tensorIso (baseChangeDomain g X n)
          (asIso (prodComparison (Over.pullback g) X X))

/-- The transported morphism is the word built from the transported group law. -/
theorem baseChange_map (g : C ⟶ B) {X A : Over B} [GrpObj A]
    (a : X ⟶ A) (n : ℕ) :
    (Over.pullback g).map (Words.DifferenceWords.map a n) =
      (DifferenceWords.baseChangeDomain g X n).hom ≫ Words.DifferenceWords.map ((Over.pullback g).map a) n := by
  induction n with
  | zero => simp [Words.DifferenceWords.map]
  | succ n ih =>
    simp only [Words.DifferenceWords.map, Functor.map_mul, Functor.map_comp, MonObj.comp_mul, ih]
    congr 1
    · simp [DifferenceWords.baseChangeDomain, Category.assoc]
    · simp [DifferenceWords.baseChangeDomain, Words.DifferenceWords.difference, div_eq_mul_inv, Functor.map_mul,
        Functor.map_comp, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]

/-- Construction uses this same actual iterated product domain. -/
theorem e07_domain (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    Words.DifferenceWords.domain X.toOver n = Albanese.Construction.ImageWords.wordDomain X n := by
  induction n with
  | zero => rfl
  | succ n ih => change Words.DifferenceWords.domain X.toOver n ⊗ _ = _; rw [ih]

@[reassoc (attr := simp)] theorem tensor_eqToHom_fst
    {X Y : Over B} (h : X = Y) (Z : Over B) :
    eqToHom (congrArg (fun W => W ⊗ Z) h) ≫ fst Y Z = fst X Z ≫ eqToHom h := by
  subst Y
  simp

@[reassoc (attr := simp)] theorem tensor_eqToHom_snd
    {X Y : Over B} (h : X = Y) (Z : Over B) :
    eqToHom (congrArg (fun W => W ⊗ Z) h) ≫ snd Y Z = snd X Z := by
  subst Y
  simp

/-- The comparison with Construction is an equality of the constructed scheme maps. -/
theorem e07_map (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (n : ℕ) :
    Words.DifferenceWords.map a n = eqToHom (e07_domain X n) ≫ Albanese.Construction.ImageWords.wordMap X A a n := by
  induction n with
  | zero => simp [Words.DifferenceWords.map, Albanese.Construction.ImageWords.wordMap]
  | succ n ih =>
    have hf : eqToHom (e07_domain X (n + 1)) ≫
        fst (Albanese.Construction.ImageWords.wordDomain X n) (X.toOver ⊗ X.toOver) =
        fst (Words.DifferenceWords.domain X.toOver n) (X.toOver ⊗ X.toOver) ≫ eqToHom (e07_domain X n) :=
      tensor_eqToHom_fst (e07_domain X n) (X.toOver ⊗ X.toOver)
    have hs : eqToHom (e07_domain X (n + 1)) ≫
        snd (Albanese.Construction.ImageWords.wordDomain X n) (X.toOver ⊗ X.toOver) =
        snd (Words.DifferenceWords.domain X.toOver n) (X.toOver ⊗ X.toOver) :=
      tensor_eqToHom_snd (e07_domain X n) (X.toOver ⊗ X.toOver)
    simp only [Words.DifferenceWords.map, Albanese.Construction.ImageWords.wordMap, MonObj.comp_mul, ih]
    congr 1
    · simp [← Category.assoc, hf]
    · simp [Words.DifferenceWords.difference, Albanese.Construction.ImageWords.differenceMap, GrpObj.comp_div,
        ← Category.assoc, hs]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.WordBaseChange.DifferenceWords
