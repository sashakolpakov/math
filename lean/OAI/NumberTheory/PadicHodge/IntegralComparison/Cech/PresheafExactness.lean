import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Presheaf Exactness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafExactness

noncomputable section

/-! The actual module-presheaf Cech functor preserves homology. -/

open _root_.CategoryTheory Limits

universe u v w

variable (R : Type u) [CommRing R] {C : Type v} [Category.{w} C]
  (E : SimplicialObject (FormalCoproduct.{u} C))

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits

instance productDegree_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits.productDegree (A := ModuleCat.{u} R) E n) where
  preservesFiniteColimits J _ _ := by
    dsimp [AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits.productDegree]
    infer_instance

instance degree_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (FormalCoproduct.cochainComplexFunctor (A := ModuleCat.{u} R) E ⋙
      HomologicalComplex.eval _ (.up ℕ) n) :=
  preservesFiniteColimits_of_natIso (AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits.degreeIso E n).symm

instance preservesFiniteLimits :
    PreservesFiniteLimits (FormalCoproduct.cochainComplexFunctor (A := ModuleCat.{u} R) E) where
  preservesFiniteLimits _ _ _ :=
    HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun _ => inferInstance)

instance preservesFiniteColimits :
    PreservesFiniteColimits (FormalCoproduct.cochainComplexFunctor (A := ModuleCat.{u} R) E) where
  preservesFiniteColimits _ _ _ :=
    HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun _ => inferInstance)

instance preservesHomology :
    (FormalCoproduct.cochainComplexFunctor (A := ModuleCat.{u} R) E).PreservesHomology := by
  infer_instance

def homologyIso (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ) (n : ℕ) :
    (((FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ)).obj K).homology n ≅
      (FormalCoproduct.cochainComplexFunctor E).obj (K.homology n) :=
  (K.sc n).mapHomologyIso (FormalCoproduct.cochainComplexFunctor E)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafExactness
