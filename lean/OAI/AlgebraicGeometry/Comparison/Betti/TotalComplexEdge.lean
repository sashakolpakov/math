import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge

/-! # Total Complex Edge -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexEdge

noncomputable section

/-! The total-complex functor comparison retains the actual horizontal augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D] (F : C ⥤ D) [F.Additive]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) (A : CochainComplex C ℕ)
  (e : ∀ q, A.X q ⟶ (K.X q).X 0)
  (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' → e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
  (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)

include he in
omit [HasCoproducts C] [HasCoproducts D] in
theorem mappedHorizontalAugmentation_comm (q q' : ℕ) (h : (ComplexShape.up ℕ).Rel q q') :
    F.map (e q) ≫ ((TotalComplexFunctor.mapBicomplex F K).d q q').f 0 =
      ((F.mapHomologicalComplex (.up ℕ)).obj A).d q q' ≫ F.map (e q') := by
  change F.map (e q) ≫ F.map ((K.d q q').f 0) = F.map (A.d q q') ≫ F.map (e q')
  rw [← F.map_comp, he q q' h, F.map_comp]

include w in
omit [HasCoproducts C] [HasCoproducts D] in
theorem mappedHorizontalAugmentation_comp_d (q : ℕ) :
    F.map (e q) ≫ ((TotalComplexFunctor.mapBicomplex F K).X q).d 0 1 = 0 := by
  change F.map (e q) ≫ F.map ((K.X q).d 0 1) = 0
  rw [← F.map_comp, w q, F.map_zero]

def mappedHorizontalEdge : (F.mapHomologicalComplex (.up ℕ)).obj A ⟶
    (TotalComplexFunctor.mapBicomplex F K).total (.up ℕ) :=
  (SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (TotalComplexFunctor.mapBicomplex F K))
    ((F.mapHomologicalComplex (.up ℕ)).obj A) (fun q => F.map (e q))
    (mappedHorizontalAugmentation_comm F K A e he)
    (mappedHorizontalAugmentation_comp_d F K A e w)

theorem mappedHorizontalEdge_comp_totalComparison :
    mappedHorizontalEdge F K A e he w ≫ TotalComplexFunctor.totalComparison F K =
      (F.mapHomologicalComplex (.up ℕ)).map ((SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he w) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (F.map (e n) ≫ (TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) n 0 n rfl) ≫
    TotalComplexFunctor.totalComparisonComponent F K n = F.map (e n ≫ K.ιTotal (.up ℕ) n 0 n rfl)
  erw [Category.assoc, TotalComplexFunctor.ι_totalComparisonComponent, ← F.map_comp]

end

end OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexEdge
