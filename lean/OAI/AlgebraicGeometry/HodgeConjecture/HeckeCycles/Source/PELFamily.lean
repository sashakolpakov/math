import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELCoherence

/-! # PEL Family -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELFamily.CM.Family

noncomputable section

/-! Identify the actual iterated PEL source with the generic universal
family at its evaluated point. Every isomorphism is the canonical
pullback comparison, retaining polarization, action, and full marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {g N : ℕ} {δ : Fin g → ℕ} {X S T U V : Scheme}
  (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N X)
  (u : S ⟶ X) (f : T ⟶ S) (h : U ⟶ T)

def iteratedIso :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (((Isogenies.NeighborCounting.ActionFamilyComparison.Family.actionFamily (A.pullback u)).pullback f).pullback h)
      ((Isogenies.NeighborCounting.ActionFamilyComparison.Family.actionFamily A).pullback (h ≫ f ≫ u)) :=
  (((Isogenies.NeighborCounting.ActionFamilyComparison.Family.actionFamilyPullbackIso A u).symm.pullback f).pullback h).trans
    (((Isogenies.NeighborCounting.ActionFamilyComparison.Family.actionFamily A).pullbackComp u f).pullback h |>.trans
      ((Isogenies.NeighborCounting.ActionFamilyComparison.Family.actionFamily A).pullbackComp (f ≫ u) h))

def sourceIso (p : V ⟶ X) (z : U ⟶ V) (w : z ≫ p = h ≫ f ≫ u) :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (((Isogenies.NeighborCounting.ActionFamilyComparison.Family.actionFamily (A.pullback u)).pullback f).pullback h)
      (((Isogenies.NeighborCounting.ActionFamilyComparison.Family.actionFamily A).pullback p).pullback z) :=
  (iteratedIso A u f h).trans ((Isogenies.NeighborCounting.ActionFamilyComparison.Family.actionFamily A).pullbackFactor z p _ w)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELFamily.CM.Family
