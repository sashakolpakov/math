import OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalCoefficientComposition

/-! # Natural Total Chain -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalChain.NaturalTotalCoefficientComposition

noncomputable section

/-! The actual nonnegative total coefficient comparison is compatible
with successive changes of coefficient category and bicomplex coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

private theorem chain {D : Type*} [Category* D] {A B C E F H : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : E ⟶ H)
    (e : B ⟶ F) (f : F ⟶ E) (g : A ⟶ F) (h : F ⟶ H)
    (hn : b ≫ c = e ≫ f) (hc : a ≫ e = g) (hm : f ≫ d = h) :
    (a ≫ b) ≫ (c ≫ d) = g ≫ h := by
  calc
    (a ≫ b) ≫ (c ≫ d) = a ≫ (b ≫ c) ≫ d := by simp only [Category.assoc]
    _ = a ≫ (e ≫ f) ≫ d := congrArg (fun q => a ≫ q ≫ d) hn
    _ = (a ≫ e) ≫ (f ≫ d) := by simp only [Category.assoc]
    _ = g ≫ h := by rw [hc, hm]

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D] [HasCoproducts.{0} E]
  (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

theorem finiteIso : AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso (F ⋙ G) K =
    AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K) ≪≫
      (G.mapHomologicalComplex (.up ℕ)).mapIso (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K) :=
  Iso.ext (TotalCoefficientComposition.TotalCoefficientComparisonComposition.comparison F G K)

variable {K} {L : HomologicalComplex₂ D (.up ℕ) (.up ℕ)}
  {M : HomologicalComplex₂ E (.up ℕ) (.up ℕ)}
  (e : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K ≅ L) (e' : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G L ≅ M)

def bicomplexIso : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (F ⋙ G) K ≅ M :=
  ((G.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).mapIso e ≪≫ e'

theorem totalIso : (G.mapHomologicalComplex (.up ℕ)).mapIso
    (NaturalTotalCoefficient.NaturalTotalCoefficientHodge.totalIso F e) ≪≫ NaturalTotalCoefficient.NaturalTotalCoefficientHodge.totalIso G e' =
      NaturalTotalCoefficient.NaturalTotalCoefficientHodge.totalIso (F ⋙ G) (bicomplexIso F G e e') := by
  apply Iso.ext
  let GH := G.mapHomologicalComplex (.up ℕ)
  let TD := HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)
  let TE := HomologicalComplex₂.totalFunctor E (.up ℕ) (.up ℕ) (.up ℕ)
  let a := GH.map (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).inv
  let b := GH.map (TD.map e.hom)
  let c := (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G L).inv
  let d := TE.map e'.hom
  let e₁ := (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K)).inv
  let f := TE.map (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap G e.hom)
  let g := (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso (F ⋙ G) K).inv
  let h := TE.map (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap G e.hom ≫ e'.hom)
  have hn : b ≫ c = e₁ ≫ f := IntegralComparison.InverseCoordinateHomology.inverse
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K))
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G L) _ _
    (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.natural G e.hom)
  have hc : a ≫ e₁ = g := (congrArg Iso.inv (finiteIso F G K)).symm
  have hm : f ≫ d = h := (TE.map_comp
    (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap G e.hom) e'.hom).symm
  exact (congrArg (fun q => q ≫ (NaturalTotalCoefficient.NaturalTotalCoefficientHodge.totalIso G e').hom)
    (GH.map_comp (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).inv (TD.map e.hom))).trans
      (chain a b c d e₁ f g h hn hc hm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalChain.NaturalTotalCoefficientComposition
