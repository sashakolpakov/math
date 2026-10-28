import Mathlib.Algebra.Homology.Homotopy

/-! # Homotopy Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.HomotopySquare.SectionComparisonHomotopySquare

noncomputable section

/-! A homotopy square of coefficient complexes induces its section
comparison homotopy after natural restriction and precomposition. -/

open _root_.CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  (T : C ⥤ D) [T.Additive] (S : C ⥤ E) [S.Additive] (S' : D ⥤ E) [S'.Additive]
  (b : S ⟶ T ⋙ S') {K I : CochainComplex C ℕ} {L J : CochainComplex D ℕ}
  {M N : CochainComplex E ℕ} (c : K ⟶ I) (c' : L ⟶ J)
  (a : (T.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)
  (t : (T.mapHomologicalComplex (.up ℕ)).obj I ⟶ J)
  (f : M ⟶ (S.mapHomologicalComplex (.up ℕ)).obj K)
  (g : N ⟶ (S'.mapHomologicalComplex (.up ℕ)).obj L) (d : M ⟶ N)
  (h : Homotopy ((T.mapHomologicalComplex (.up ℕ)).map c ≫ t) (a ≫ c'))
  (hs : f ≫ (b.mapHomologicalComplex (.up ℕ)).app K ≫ (S'.mapHomologicalComplex (.up ℕ)).map a = d ≫ g)

theorem left_eq : (f ≫ (S.mapHomologicalComplex (.up ℕ)).map c) ≫
    ((b.mapHomologicalComplex (.up ℕ)).app I ≫ (S'.mapHomologicalComplex (.up ℕ)).map t) =
      (f ≫ (b.mapHomologicalComplex (.up ℕ)).app K) ≫
        (S'.mapHomologicalComplex (.up ℕ)).map ((T.mapHomologicalComplex (.up ℕ)).map c ≫ t) := by
  have hn := (b.mapHomologicalComplex (.up ℕ)).naturality c
  let F := S'.mapHomologicalComplex (.up ℕ)
  have hp := (congrArg (fun q => q ≫ F.map t) hn).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun q => (b.mapHomologicalComplex (.up ℕ)).app K ≫ q)
        (F.map_comp ((T.mapHomologicalComplex (.up ℕ)).map c) t).symm))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => f ≫ q)
      (Category.assoc ((S.mapHomologicalComplex (.up ℕ)).map c)
        ((b.mapHomologicalComplex (.up ℕ)).app I) (F.map t)).symm).trans
        ((congrArg (fun q => f ≫ q) hp).trans (Category.assoc _ _ _).symm))

include hs in
theorem right_eq : (f ≫ (b.mapHomologicalComplex (.up ℕ)).app K) ≫
    (S'.mapHomologicalComplex (.up ℕ)).map (a ≫ c') =
      (d ≫ g) ≫ (S'.mapHomologicalComplex (.up ℕ)).map c' := by
  let F := S'.mapHomologicalComplex (.up ℕ)
  exact (congrArg (fun q => (f ≫ (b.mapHomologicalComplex (.up ℕ)).app K) ≫ q) (F.map_comp a c')).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ F.map c') ((Category.assoc _ _ _).trans hs)))

def homotopy : Homotopy
    ((f ≫ (S.mapHomologicalComplex (.up ℕ)).map c) ≫
      ((b.mapHomologicalComplex (.up ℕ)).app I ≫ (S'.mapHomologicalComplex (.up ℕ)).map t))
    ((d ≫ g) ≫ (S'.mapHomologicalComplex (.up ℕ)).map c') :=
  (Homotopy.ofEq (left_eq T S S' b c t f)).trans
    (((S'.mapHomotopy h).compLeft (f ≫ (b.mapHomologicalComplex (.up ℕ)).app K)).trans
      (Homotopy.ofEq (right_eq T S S' b c' a f g d hs)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.HomotopySquare.SectionComparisonHomotopySquare
