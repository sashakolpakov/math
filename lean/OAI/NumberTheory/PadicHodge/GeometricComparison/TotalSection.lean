import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalExtensionTransformation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalExtensionComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFinite

/-! # Total Section -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TotalSection.TotalSectionPullbackNaturality

noncomputable section

/-! The actual integer total comparison commutes with a section pullback and an actual map of coefficient bicomplexes. -/

open _root_.CategoryTheory Limits _root_.HomologicalComplex₂

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  [HasFiniteCoproducts C] [HasFiniteCoproducts D] [HasFiniteCoproducts E]
  (F : C ⥤ D) (Γ : C ⥤ E) (Λ : D ⥤ E) [F.Additive] [Γ.Additive] [Λ.Additive]
  (a : Γ ⟶ F ⋙ Λ)
  {K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)} {L : HomologicalComplex₂ D (.up ℕ) (.up ℕ)}
  (b : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K ⟶ L)

def resolvedMap : (F.mapHomologicalComplex (.up ℤ)).obj ((TotalFinite.IntegerTotalFunctor.functor C).obj K) ⟶
    (TotalFinite.IntegerTotalFunctor.functor D).obj L :=
  (Finite.TotalIso.FiniteTotalExtension.iso F K).inv ≫ (TotalFinite.IntegerTotalFunctor.functor D).map b

def sectionMap : (Γ.mapHomologicalComplex (.up ℤ)).obj ((TotalFinite.IntegerTotalFunctor.functor C).obj K) ⟶
    (Λ.mapHomologicalComplex (.up ℤ)).obj ((TotalFinite.IntegerTotalFunctor.functor D).obj L) :=
  (NatTrans.mapHomologicalComplex a (.up ℤ)).app ((TotalFinite.IntegerTotalFunctor.functor C).obj K) ≫
    (Λ.mapHomologicalComplex (.up ℤ)).map (resolvedMap F b)

def cochainMap : (TotalFinite.IntegerTotalFunctor.functor E).obj (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex Γ K) ⟶
    (TotalFinite.IntegerTotalFunctor.functor E).obj (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex Λ L) :=
  (TotalFinite.IntegerTotalFunctor.functor E).map
    (Finite.TotalTransformation.FiniteTotalTransformation.bicomplexMap a K ≫ Finite.TotalIso.FiniteTotalNaturality.map Λ b)

theorem comparison_square : cochainMap F Γ Λ a b ≫ (Finite.TotalIso.FiniteTotalExtension.iso Λ L).hom =
    (Finite.TotalIso.FiniteTotalExtension.iso Γ K).hom ≫ sectionMap F Γ Λ a b := by
  let M := TotalFinite.IntegerTotalFunctor.functor E
  let N := Λ.mapHomologicalComplex (.up ℤ)
  let m := (TotalFinite.IntegerTotalFunctor.functor D).map b
  have h₂ : M.map (Finite.TotalIso.FiniteTotalNaturality.map Λ b) ≫ (Finite.TotalIso.FiniteTotalExtension.iso Λ L).hom =
      (Finite.TotalIso.FiniteTotalExtension.iso (F ⋙ Λ) K).hom ≫ N.map (resolvedMap F b) :=
    (TotalFinite.FiniteTotalExtensionNaturality.naturality Λ b).trans
      ((congrArg (fun k => k ≫ N.map m) (Finite.TotalExtensionComposition.FiniteTotalExtensionComposition.hom_inverse F Λ K)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun k => (Finite.TotalIso.FiniteTotalExtension.iso (F ⋙ Λ) K).hom ≫ k)
            (N.map_comp (Finite.TotalIso.FiniteTotalExtension.iso F K).inv m).symm)))
  have h₃ := Finite.TotalExtensionTransformation.FiniteTotalExtensionTransformation.naturality a K
  exact (congrArg (fun k => k ≫ (Finite.TotalIso.FiniteTotalExtension.iso Λ L).hom)
    (M.map_comp (Finite.TotalTransformation.FiniteTotalTransformation.bicomplexMap a K) (Finite.TotalIso.FiniteTotalNaturality.map Λ b))).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => M.map (Finite.TotalTransformation.FiniteTotalTransformation.bicomplexMap a K) ≫ k) h₂).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ N.map (resolvedMap F b)) h₃).trans (Category.assoc _ _ _)))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TotalSection.TotalSectionPullbackNaturality
