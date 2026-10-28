import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.KanFibres
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatModuleKanExtension

/-! # Restriction Injectives -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.RestrictionInjectives.FramedCrystallineRestrictionInjectives

noncomputable section

/-!
# Restriction to framed crystalline sheaves preserves injectives

The pointwise left Kan extension is computed by a direct sum over actual
coordinate lifts. Exactness of module coproducts therefore makes the
left adjoint on sheaves exact, so framed restriction preserves injectives.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k (OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ a

instance comma_exactColimits
    (Q : (Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))ᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (U).op Q) V := by
  have : AB4OfSize.{u} V := AB4OfSize_shrink.{u, u + 1} V
  exact hasExactColimitsOfShape_of_final V
    (KanFibres.FramedCrystallineKanFibres.inclusion p k B σ a Q.unop)

instance lan_finiteLimits : PreservesFiniteLimits
    ((U).op.lan : ((Category.FramedCrystallineCategory.Object p k B σ a)ᵒᵖ ⥤ V) ⥤
      (Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))ᵒᵖ ⥤ V) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
  intro T _ _
  apply preservesLimitsOfShape_of_evaluation
    ((U).op.lan : ((Category.FramedCrystallineCategory.Object p k B σ a)ᵒᵖ ⥤ V) ⥤
      (Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))ᵒᵖ ⥤ V) T
  intro Q
  exact preservesLimitsOfShape_of_natIso
    (NumberTheory.PadicHodge.IntegralComparison.FlatModuleKanExtension.evaluationIso
      (Site.CoefficientRing p k) (U).op Q).symm

instance sheafLeftAdjoint_finiteLimits : PreservesFiniteLimits
    (Functor.sheafPullbackConstruction.sheafPullback U V K J) := by
  change PreservesFiniteLimits (sheafToPresheaf K V ⋙ (U).op.lan ⋙ presheafToSheaf J V)
  have : PreservesFiniteLimits ((U).op.lan ⋙ presheafToSheaf J V) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

instance restriction_preservesInjectives :
    (SheafExactness.FramedCrystallineSheafExactness.restriction p k B σ a V).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U V K J)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.RestrictionInjectives.FramedCrystallineRestrictionInjectives
