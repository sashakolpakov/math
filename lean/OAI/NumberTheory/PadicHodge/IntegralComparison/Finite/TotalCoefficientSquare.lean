import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison
import OAI.AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor

/-! # Total Coefficient Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.TotalCoefficientSquare

noncomputable section

/-! A commuting coefficient square of genuine bicomplex maps gives
its exact square on the original finite total complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂
universe uA vA uB vB
variable {A : Type uA} [Category.{vA} A] [Preadditive A]
  {B : Type uB} [Category.{vB} B] [Preadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B] [HasFiniteBiproducts A]
  (G : A ⥤ B) [G.Additive]
  {K L : HomologicalComplex₂ A (.up ℕ) (.up ℕ)}
  {K' L' : HomologicalComplex₂ B (.up ℕ) (.up ℕ)}
  (eK : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G K ≅ K') (eL : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G L ≅ L')

def iso : (G.mapHomologicalComplex (.up ℕ)).obj (K.total (.up ℕ)) ≅ K'.total (.up ℕ) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G K).symm ≪≫ total.mapIso eK (.up ℕ)

theorem comparison (φ : K ⟶ L) (ψ : K' ⟶ L')
    (h : AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G φ ≫ eL.hom = eK.hom ≫ ψ) :
    (G.mapHomologicalComplex (.up ℕ)).map (total.map φ (.up ℕ)) ≫ (iso G eL).hom =
      (iso G eK).hom ≫ total.map ψ (.up ℕ) := by
  let dK := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G K
  let dL := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G L
  have hn : total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G φ) (.up ℕ) ≫ dL.hom =
      dK.hom ≫ (G.mapHomologicalComplex (.up ℕ)).map (total.map φ (.up ℕ)) :=
    AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.totalComparison_naturality G φ
  have hi : (G.mapHomologicalComplex (.up ℕ)).map (total.map φ (.up ℕ)) ≫ dL.inv =
      dK.inv ≫ total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G φ) (.up ℕ) := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun f => dK.inv ≫ f ≫ dL.inv) hn.symm
  have ht : total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G φ) (.up ℕ) ≫ total.map eL.hom (.up ℕ) =
      total.map eK.hom (.up ℕ) ≫ total.map ψ (.up ℕ) := by
    simpa only [total.map_comp] using congrArg (fun a => total.map a (.up ℕ)) h
  change (G.mapHomologicalComplex (.up ℕ)).map (total.map φ (.up ℕ)) ≫
      (dL.inv ≫ total.map eL.hom (.up ℕ)) =
    (dK.inv ≫ total.map eK.hom (.up ℕ)) ≫ total.map ψ (.up ℕ)
  rw [← Category.assoc, hi, Category.assoc, ht, ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.TotalCoefficientSquare
