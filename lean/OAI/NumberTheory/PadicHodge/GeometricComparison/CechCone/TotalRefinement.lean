import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctor

/-! # Total Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinement.CechConeTotalRefinement

noncomputable section

/-! Refinement of a covering family acts on the original total complex
and preserves the canonical augmentation of any coefficient cone. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι κ : Type} (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

local instance hasTotal (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

def bicomplexMap (P : Cᵒᵖ ⥤ CochainComplex A ℕ) :
    Total.CechConeTotal.bicomplex U P ⟶ Total.CechConeTotal.bicomplex V P :=
  (HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).map
    (NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P)

def map (P : Cᵒᵖ ⥤ CochainComplex A ℕ) : Total.CechConeTotal.total U P ⟶ Total.CechConeTotal.total V P :=
  HomologicalComplex₂.total.map (bicomplexMap U V r P) (.up ℕ)

omit [HasCoproducts.{0} A] in
theorem naturality {P Q : Cᵒᵖ ⥤ CochainComplex A ℕ} (a : P ⟶ Q) :
    (TotalFunctor.CechConeTotalFunctor.functor U).map a ≫ CechConeTotalRefinement.map U V r Q =
      CechConeTotalRefinement.map U V r P ≫ (TotalFunctor.CechConeTotalFunctor.functor V).map a := by
  let F := HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map (NonemptyCech.Refinement.NonemptyCechRefinement.naturality U V r a)).trans (F.map_comp _ _))

variable (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (M : CochainComplex A ℕ)
  (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

omit [HasCoproducts.{0} A] in
theorem augmentation : Total.CechConeTotal.augmentation U P M η ≫ CechConeTotalRefinement.map U V r P =
    Total.CechConeTotal.augmentation V P M η := by
  ext q : 1
  let K := Total.CechConeTotal.bicomplex U P
  let L := Total.CechConeTotal.bicomplex V P
  let a := bicomplexMap U V r P
  have hq := congrArg (fun f => f.f q) (NonemptyCech.Refinement.NonemptyCechRefinement.restriction U V r P M η ⦋0⦌)
  change Total.CechConeTotal.component U P M η q ≫ (a.f q).f 0 =
    Total.CechConeTotal.component V P M η q at hq
  change (Total.CechConeTotal.component U P M η q ≫ K.ιTotal (.up ℕ) q 0 q rfl) ≫
      (HomologicalComplex₂.total.map a (.up ℕ)).f q =
    Total.CechConeTotal.component V P M η q ≫ L.ιTotal (.up ℕ) q 0 q rfl
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => Total.CechConeTotal.component U P M η q ≫ k)
      (HomologicalComplex₂.ιTotal_map K L a (.up ℕ) q 0 q rfl)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ L.ιTotal (.up ℕ) q 0 q rfl) hq)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinement.CechConeTotalRefinement
