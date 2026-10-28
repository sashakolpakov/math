import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechHomotopy

/-! # Homology Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.HomologyFunctor

noncomputable section

/-! The original supported Čech cohomology as a functor, with direct
identities for an already constructed comparison homotopy. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
section

universe u v w
variable {R : Type u} [CommRing R] {C : Type v} [Preorder C] [HasFiniteProducts C]
  {ι : Type v} [LinearOrder ι] (U : ι → C)
  [HasProducts.{v} (ModuleCat.{w} R)]

def functor (n : ℕ) : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ ⥤ ModuleCat.{w} R :=
  (AugmentedOrdered.CechFunctor.functor U).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{w} R) (.up ℕ) (.up ℕ) (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (.up ℕ) n

theorem homotopy {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} {a b : K ⟶ L}
    (h : Homotopy a b) (n : ℕ) : (functor U n).map a = (functor U n).map b :=
  AugmentedOrdered.CechHomotopy.homology U h n

theorem homotopy_comp {K L M : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ}
    {a : K ⟶ M} {b : K ⟶ L} {c : L ⟶ M} (h : Homotopy a (b ≫ c)) (n : ℕ) :
    (functor U n).map a = (functor U n).map b ≫ (functor U n).map c :=
  (homotopy U h n).trans ((functor U n).map_comp b c)

end

namespace MappedComparisonEquality

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

theorem square {A B E A' : C} {a : A ⟶ B} {b : B ⟶ E}
    {c : A ⟶ A'} {d : A' ⟶ E} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  simpa only [F.map_comp] using congrArg F.map h

theorem triple {A B E Z A' : C} {a : A ⟶ B} {b : B ⟶ E} {c : E ⟶ Z}
    {d : A ⟶ A'} {e : A' ⟶ Z} (h : (a ≫ b) ≫ c = d ≫ e) :
    (F.map a ≫ F.map b) ≫ F.map c = F.map d ≫ F.map e := by
  simpa only [F.map_comp] using congrArg F.map h

theorem factorization {A B E : C} {q : A ⟶ E} {a : A ⟶ B} {b : B ⟶ E}
    (h : q = a ≫ b) : F.map q = F.map a ≫ F.map b := by
  simpa only [F.map_comp] using congrArg F.map h

end MappedComparisonEquality

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.HomologyFunctor
