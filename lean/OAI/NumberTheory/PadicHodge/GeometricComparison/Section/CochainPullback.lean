import Mathlib.Algebra.Homology.Additive

/-! # Cochain Pullback -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback.SectionCochainPullback

/-! A section transformation and a coefficient-complex pullback give
a typed map between the original section complexes. -/

open _root_.CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  (T : C ⥤ D) [T.Additive] (S : C ⥤ E) [S.Additive] (S' : D ⥤ E) [S'.Additive]
  (b : S ⟶ T ⋙ S') {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (a : (T.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)

def map : (S.mapHomologicalComplex (.up ℕ)).obj K ⟶ (S'.mapHomologicalComplex (.up ℕ)).obj L :=
  (b.mapHomologicalComplex (.up ℕ)).app K ≫ (S'.mapHomologicalComplex (.up ℕ)).map a

theorem map_eq : SectionCochainPullback.map T S S' b a =
    (b.mapHomologicalComplex (.up ℕ)).app K ≫ (S'.mapHomologicalComplex (.up ℕ)).map a := rfl

end NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback.SectionCochainPullback

namespace NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback.SectionCochainPullbackFactorization

/-! Section pullback respects precomposition by the original source
complex maps and postcomposition by target complex maps. -/

open _root_.CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  (T : C ⥤ D) [T.Additive] (S : C ⥤ E) [S.Additive] (S' : D ⥤ E) [S'.Additive]
  (b : S ⟶ T ⋙ S')
  {K L : CochainComplex C ℕ} {M N : CochainComplex D ℕ}

theorem precompose (r : K ⟶ L) (a : (T.mapHomologicalComplex (.up ℕ)).obj L ⟶ M) :
    (S.mapHomologicalComplex (.up ℕ)).map r ≫ SectionCochainPullback.map T S S' b a =
      SectionCochainPullback.map T S S' b ((T.mapHomologicalComplex (.up ℕ)).map r ≫ a) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ (S'.mapHomologicalComplex (.up ℕ)).map a)
      ((b.mapHomologicalComplex (.up ℕ)).naturality r)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun q => (b.mapHomologicalComplex (.up ℕ)).app K ≫ q)
            ((S'.mapHomologicalComplex (.up ℕ)).map_comp
              ((T.mapHomologicalComplex (.up ℕ)).map r) a).symm)))

theorem postcompose (a : (T.mapHomologicalComplex (.up ℕ)).obj K ⟶ M) (r : M ⟶ N) :
    SectionCochainPullback.map T S S' b a ≫ (S'.mapHomologicalComplex (.up ℕ)).map r =
      SectionCochainPullback.map T S S' b (a ≫ r) :=
  (Category.assoc _ _ _).trans
    (congrArg (fun q => (b.mapHomologicalComplex (.up ℕ)).app K ≫ q)
      ((S'.mapHomologicalComplex (.up ℕ)).map_comp a r).symm)

end NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback.SectionCochainPullbackFactorization

end

end OAI
