import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TotalProjectionNaturality

/-! # Coefficient Forget -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientForget

noncomputable section

/-! Coefficient change preserves the literal support-forgetting map,
including the actual empty-intersection identification. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vA uA vB uB
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientTotal
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G]

omit [Preadditive A] [Preadditive B] [G.Additive] in
theorem zero (P : Cᵒᵖ ⥤ A) :
    (CoefficientChange.objectIso U G P 0).hom ≫ (AugmentedOrdered.CechZero.zeroIso U (P ⋙ G)).hom =
      G.map (AugmentedOrdered.CechZero.zeroIso U P).hom := by
  change piComparison G (fun a : AugmentedOrdered.Cech.Index ι 0 => P.obj (op ((AugmentedOrdered.Cech.formal U 0).obj a))) ≫
    (Pi.π (fun a : AugmentedOrdered.Cech.Index ι 0 => G.obj (P.obj (op ((AugmentedOrdered.Cech.formal U 0).obj a)))) AugmentedOrdered.CechZero.emptyIndex ≫
      G.map (P.map (AugmentedOrdered.CechZero.emptyProductMap U AugmentedOrdered.CechZero.emptyIndex).op)) = _
  rw [← Category.assoc, piComparison_comp_π, ← G.map_comp]
  rfl

variable [HasCoproducts.{0} A] [HasCoproducts.{0} B]

omit [HasProducts A] [HasProducts B] [PreservesLimitsOfSize.{u, u, vA, vB, uA, uB} G] in
theorem projection (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) (p q n : ℕ) :
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent G K n ≫ G.map ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) p q n) =
      (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G K)) p q n := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  rw [← Category.assoc, AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent, ← G.map_comp,
    AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat, AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat]
  by_cases ha : a = p
  · subst a
    by_cases hb : b = q
    · subst b
      simp [HomologicalComplex₂.XXIsoOfEq]
      rfl
    · simp [hb]
  · simp [ha]

variable [HasFiniteBiproducts A] (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ)

theorem comparison : (CoefficientTotal.totalIso U G K).hom ≫ AugmentedOrdered.CechForget.forgetSupport U (CoefficientTotal.mapped G K) =
    (G.mapHomologicalComplex (.up ℕ)).map (AugmentedOrdered.CechForget.forgetSupport U K) := by
  let T := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (AugmentedOrdered.CechFunctor.bicomplex U K)
  apply (cancel_epi T.hom).mp
  change T.hom ≫ ((T.inv ≫ (HomologicalComplex₂.total.map (CoefficientTotal.bicomplexIso U G K).hom (.up ℕ))) ≫
    AugmentedOrdered.CechForget.forgetSupport U (CoefficientTotal.mapped G K)) = _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  apply HomologicalComplex.Hom.ext
  funext n
  change (HomologicalComplex₂.total.map (CoefficientTotal.bicomplexIso U G K).hom (.up ℕ)).f n ≫
    ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (AugmentedOrdered.CechFunctor.bicomplex U (CoefficientTotal.mapped G K))) n 0 n ≫ (AugmentedOrdered.CechZero.zeroIso U ((CoefficientTotal.mapped G K).X n)).hom) =
      AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent G (AugmentedOrdered.CechFunctor.bicomplex U K) n ≫
        G.map ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (AugmentedOrdered.CechFunctor.bicomplex U K)) n 0 n ≫ (AugmentedOrdered.CechZero.zeroIso U (K.X n)).hom)
  rw [← Category.assoc, TotalProjectionNaturality.map, Category.assoc,
    G.map_comp, ← Category.assoc (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent G (AugmentedOrdered.CechFunctor.bicomplex U K) n),
    projection]
  exact congrArg (fun a => (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G (AugmentedOrdered.CechFunctor.bicomplex U K))) n 0 n ≫ a)
    (zero U G (K.X n))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientForget
