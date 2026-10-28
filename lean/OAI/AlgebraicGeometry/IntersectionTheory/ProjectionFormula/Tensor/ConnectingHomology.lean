import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CocycleHomology
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SplitSequenceCochain
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.CochainShift
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! # Connecting Homology -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ConnectingHomology

noncomputable section

/-! The native tensor cone boundary agrees on homology with the boundary
of the split sequence, through its canonical cone-to-quotient map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CochainComplex _root_.CochainComplex.HomComplex

variable (R : Type) [CommRing R]
  (S : ShortComplex (CochainComplex (ModuleCat.{0} R) ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval _ _ n)).Splitting)
  (K : CochainComplex (ModuleCat.{0} R) ℤ)

theorem connecting (n m : ℤ) (h : 1 + n = m) :
    CocycleHomology.map R (Tensor.Cochain.mapCocycle R K (-mappingCone.fst S.f)) n m h =
      HomologicalComplex.homologyMap
        ((Homotopy.complexFunctor R K).map (mappingCone.descShortComplex S)) n ≫
      CocycleHomology.map R (Tensor.Cochain.mapCocycle R K (cocycleOfDegreewiseSplit S σ)) n m h := by
  rw [← CocycleHomology.precomp]
  apply CocycleHomology.map_eq R _ _
    (Tensor.Cochain.map R K (SplitSequenceCochain.comparisonHomotopy R S σ))
  change Tensor.Cochain.map R K (-mappingCone.fst S.f).1 =
    (Cochain.ofHom ((Homotopy.complexFunctor R K).map (mappingCone.descShortComplex S))).comp
      (Tensor.Cochain.map R K (cocycleOfDegreewiseSplit S σ).1) (zero_add 1) +
    δ 0 1 (Tensor.Cochain.map R K (SplitSequenceCochain.comparisonHomotopy R S σ))
  simpa only [Cocycle.coe_neg, Tensor.Cochain.map_neg] using
    SplitSequenceCochain.tensor_cone_connecting R S σ K

theorem mapCocycle_postcomp {P Q U : CochainComplex (ModuleCat.{0} R) ℤ} {a : ℤ}
    (z : Cocycle P Q a) (f : Q ⟶ U) :
    Tensor.Cochain.mapCocycle R K (z.postcomp f) =
      (Tensor.Cochain.mapCocycle R K z).postcomp ((Homotopy.complexFunctor R K).map f) := by
  apply Subtype.ext
  simp only [Tensor.Cochain.mapCocycle_coe, Cocycle.postcomp, Cocycle.mk_coe,
    Tensor.Cochain.map_comp, Tensor.Cochain.map_ofHom]

theorem comp_triangle {P Q U : CochainComplex (ModuleCat.{0} R) ℤ}
    (f : P ⟶ Q) (g : Q ⟶ U) (n m : ℤ) (h : 1 + n = m) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) 0).shiftMap
      (ShiftedHom.map (mappingConeCompTriangle f g).mor₃
        (Homotopy.complexFunctor R K)) n m h =
    CocycleHomology.map R (Tensor.Cochain.mapCocycle R K (-mappingCone.fst g)) n m h ≫
      HomologicalComplex.homologyMap ((Homotopy.complexFunctor R K).map (mappingCone.inr f)) m := by
  have he : ShiftedHom.map (mappingConeCompTriangle f g).mor₃
      (Homotopy.complexFunctor R K) =
      Cocycle.equivHomShift.symm (Tensor.Cochain.mapCocycle R K (-mappingCone.fst g)) ≫
        ((Homotopy.complexFunctor R K).map (mappingCone.inr f))⟦(1 : ℤ)⟧' := by
    change (Homotopy.complexFunctor R K).map
        ((mappingCone.triangle g).mor₃ ≫ (mappingCone.inr f)⟦(1 : ℤ)⟧') ≫
      ((Homotopy.complexFunctor R K).commShiftIso (1 : ℤ)).hom.app (mappingCone f) = _
    rw [CategoryTheory.Functor.map_comp, Category.assoc,
      CategoryTheory.Functor.commShiftIso_hom_naturality, ← Category.assoc]
    change ((Homotopy.complexFunctor R K).map
      (Cocycle.homOf ((-mappingCone.fst g).rightShift 1 0 (zero_add 1))) ≫ _) ≫ _ = _
    congr 1
    exact CochainShift.homOf_rightShift R K (-mappingCone.fst g)
  rw [he, CategoryTheory.Functor.shiftMap_comp]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ConnectingHomology
