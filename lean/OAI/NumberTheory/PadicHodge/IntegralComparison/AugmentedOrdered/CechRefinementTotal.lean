import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor

/-! # Cech Refinement Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementTotal

noncomputable section

/-! Refinement of supported ordered Čech totals, with the ambient
section term fixed and the original full refinement on positive degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

omit [HasCoproducts D] in
theorem naturality {P Q : Cᵒᵖ ⥤ D} (a : P ⟶ Q) :
    CechFunctor.complexMap U a ≫ CechRefinement.map U V r Q =
      CechRefinement.map U V r P ≫ CechFunctor.complexMap V a := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    change CechFunctor.objectMap U a 0 ≫
        (CechZero.zeroIso U Q).hom ≫
        (CechZero.zeroIso V Q).inv =
      ((CechZero.zeroIso U P).hom ≫
        (CechZero.zeroIso V P).inv) ≫
          CechFunctor.objectMap V a 0
    apply (cancel_mono (CechZero.zeroIso V Q).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [CechFunctor.objectMap]
    rw [← Category.assoc, CechZero.zeroIso_naturality]
    rw [Category.assoc, CechZero.zeroIso_naturality]
    rw [← Category.assoc (CechZero.zeroIso V P).inv,
      Iso.inv_hom_id, Category.id_comp]
  | succ n =>
    exact congrArg (fun f => f.f n)
      ((OrderedCech.Refinement.transformation U V r).naturality a)

def transformation : CechFunctor.functor U (D := D) ⟶
    CechFunctor.functor V (D := D) where
  app P := CechRefinement.map U V r P
  naturality _ _ a := CechRefinementTotal.naturality U V r a

def bicomplexMap (K : CochainComplex (Cᵒᵖ ⥤ D) ℕ) :
    ((CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((CechFunctor.functor V).mapHomologicalComplex (.up ℕ)).obj K :=
  (NatTrans.mapHomologicalComplex (transformation U V r) (.up ℕ)).app K

def totalMap (K : CochainComplex (Cᵒᵖ ⥤ D) ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap U V r K) (.up ℕ)

theorem total_quasiIso {R : Type v} [Ring R]
    (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ)
    (hK : ∀ q, QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (K.X q))) :
    QuasiIso (totalMap U V r K) := by
  apply AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex.total_map_quasiIso_of_columns
  intro q
  let : QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (K.X q)) := hK q
  exact CechRefinementQuasiIso.quasiIso U V r (K.X q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementTotal
