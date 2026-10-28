import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Total Iso -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso.FiniteTotalExtension

/-! Actual finite-diagonal totalization and native integer extension commute with additive functors. -/

open _root_.CategoryTheory Limits _root_.HomologicalComplex₂

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
  (F : C ⥤ D) [F.Additive] (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

local instance : K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance : (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K)

def iso : ((AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).total (.up ℕ)).extend ComplexShape.embeddingUpNat ≅
    (F.mapHomologicalComplex (.up ℤ)).obj ((K.total (.up ℕ)).extend ComplexShape.embeddingUpNat) :=
  (ComplexShape.embeddingUpNat.extendFunctor D).mapIso (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K) ≪≫
    (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat (K.total (.up ℕ))).symm

end NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso.FiniteTotalExtension

namespace NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso.FiniteTotalNaturality

/-! Naturality of the finite total scalar comparison for actual maps of bicomplexes. -/

open _root_.CategoryTheory Limits _root_.HomologicalComplex₂

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasFiniteCoproducts C] [HasFiniteCoproducts D] (F : C ⥤ D) [F.Additive]

local instance (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance (K : HomologicalComplex₂ D (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

def map {K L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)} (φ : K ⟶ L) :
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K ⟶ AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F L :=
  ((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).map φ

theorem naturality {K L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)} (φ : K ⟶ L) :
    total.map (FiniteTotalNaturality.map F φ) (.up ℕ) ≫ (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F L).hom =
      (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).hom ≫
        (F.mapHomologicalComplex (.up ℕ)).map (total.map φ (.up ℕ)) := by
  ext n : 1
  apply total.hom_ext
  intro q p h
  change (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫
      (total.map (FiniteTotalNaturality.map F φ) (.up ℕ)).f n ≫ AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonComponent F L n =
    (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫
      AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonComponent F K n ≫ F.map ((total.map φ (.up ℕ)).f n)
  rw [← Category.assoc, ιTotal_map, Category.assoc, AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.ι_finiteTotalComparisonComponent,
    ← Category.assoc, AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.ι_finiteTotalComparisonComponent]
  exact (F.map_comp ((φ.f q).f p) (L.ιTotal (.up ℕ) q p n h)).symm.trans
    ((congrArg F.map (ιTotal_map K L φ (.up ℕ) q p n h).symm).trans
      (F.map_comp (K.ιTotal (.up ℕ) q p n h) ((total.map φ (.up ℕ)).f n)))

end NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso.FiniteTotalNaturality

namespace NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso.FiniteTotalComposition

/-! The actual finite total comparison respects composition of additive coefficient functors. -/

open _root_.CategoryTheory Limits _root_.HomologicalComplex₂

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasFiniteCoproducts C] [HasFiniteCoproducts D] [HasFiniteCoproducts E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

local instance (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance (K : HomologicalComplex₂ D (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance (K : HomologicalComplex₂ E (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

theorem hom (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) :
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K)).hom ≫
        (G.mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).hom =
      (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso (F ⋙ G) K).hom := by
  ext n : 1
  apply total.hom_ext
  intro q p h
  change (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K)).ιTotal (.up ℕ) q p n h ≫
      AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonComponent G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K) n ≫
        G.map (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonComponent F K n) =
    (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (F ⋙ G) K).ιTotal (.up ℕ) q p n h ≫
      AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonComponent (F ⋙ G) K n
  rw [← Category.assoc, AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.ι_finiteTotalComparisonComponent,
    AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.ι_finiteTotalComparisonComponent]
  exact (G.map_comp _ _).symm.trans
    (congrArg G.map (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.ι_finiteTotalComparisonComponent F K q p n h))

theorem hom_inverse (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) :
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K)).hom =
      (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso (F ⋙ G) K).hom ≫
        (G.mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).inv := by
  let e := (G.mapHomologicalComplex (.up ℕ)).mapIso (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K)
  exact (e.comp_inv_eq.mpr (FiniteTotalComposition.hom F G K).symm).symm

end NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso.FiniteTotalComposition

end

end OAI
