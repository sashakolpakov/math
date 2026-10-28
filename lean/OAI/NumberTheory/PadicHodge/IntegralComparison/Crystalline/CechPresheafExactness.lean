import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ExactProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafExactness

/-! # Cech Presheaf Exactness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CechPresheafExactness

noncomputable section

/-! The actual Cech functor preserves homology in the original crystalline coefficient universe. -/

open _root_.CategoryTheory Limits

universe u v w

variable (B : Type u) [CommRing B] {C : Type v} [Category.{w} C]
  (E : SimplicialObject (FormalCoproduct.{u} C))

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

local instance fullLimits : HasLimits (ModuleCat.{u + 2} R) :=
  ModuleCat.hasLimitsOfSize.{u + 2, u + 2, u + 2, u + 1}

local instance smallLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}

local instance smallProducts : HasProducts.{u} (ModuleCat.{u + 2} R) :=
  fun I => (smallLimits B).has_limits_of_shape (Discrete I)

local instance exactProducts : AB4StarOfSize.{u} (ModuleCat.{u + 2} R) :=
  Module.ExactProducts.smallProducts.{u + 1, u, u + 2} R

instance productDegree_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits.productDegree (A := ModuleCat.{u + 2} R) E n) where
  preservesFiniteColimits J _ _ := by
    dsimp [AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits.productDegree]
    infer_instance

instance degree_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (FormalCoproduct.cochainComplexFunctor (A := ModuleCat.{u + 2} R) E ⋙
      HomologicalComplex.eval _ (.up ℕ) n) :=
  preservesFiniteColimits_of_natIso (AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits.degreeIso E n).symm

instance preservesFiniteLimits :
    PreservesFiniteLimits (FormalCoproduct.cochainComplexFunctor (A := ModuleCat.{u + 2} R) E) where
  preservesFiniteLimits _ _ _ :=
    HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun _ => inferInstance)

instance preservesFiniteColimits :
    PreservesFiniteColimits (FormalCoproduct.cochainComplexFunctor (A := ModuleCat.{u + 2} R) E) where
  preservesFiniteColimits _ _ _ :=
    HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun _ => inferInstance)

instance preservesHomology :
    (FormalCoproduct.cochainComplexFunctor (A := ModuleCat.{u + 2} R) E).PreservesHomology := by
  infer_instance

def homologyIso (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u + 2} R) ℕ) (n : ℕ) :
    (((FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ)).obj K).homology n ≅
      (FormalCoproduct.cochainComplexFunctor E).obj (K.homology n) :=
  (K.sc n).mapHomologyIso (FormalCoproduct.cochainComplexFunctor E)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CechPresheafExactness
