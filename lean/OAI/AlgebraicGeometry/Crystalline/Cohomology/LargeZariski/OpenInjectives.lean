import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.CechRestriction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.OpenKanEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Colimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Open Injectives -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.OpenInjectives.LargeZariskiOpenInjectives

noncomputable section

/-!
# Open restriction preserves injectives at the native coefficient size

The left Kan comma category is empty outside the open and has a
terminal object inside. The resulting exact extension by zero proves
that actual open restriction preserves injective module sheaves.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

abbrev Modules := ModuleCat.{u + 1} R

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.OpenInjectives.LargeZariskiOpenInjectives.Modules R
local notation "J" => Opens.grothendieckTopology Y
local notation "K" => Opens.grothendieckTopology X
local notation "L" => Functor.op f.opensFunctor

local instance moduleColimits : HasColimitsOfSize.{u, u} V :=
  ModuleCat.hasColimitsOfSize.{u + 1, u + 1, u, u} R

instance comma_exactColimits (Q : X.Opensᵒᵖ) : HasExactColimitsOfShape (CostructuredArrow L Q) V := by
  classical
  by_cases h : Nonempty (CostructuredArrow L Q)
  · obtain ⟨T⟩ := h
    have hQ : Q.unop ≤ f.opensRange :=
      (leOfHom T.hom.unop).trans (f.image_le_opensRange T.left.unop)
    have he : f ''ᵁ (f ⁻¹ᵁ Q.unop) = Q.unop := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hQ]
    let P := op (f ⁻¹ᵁ Q.unop)
    let e : (L).obj P ≅ Q := eqToIso (congrArg op he)
    have ht : HasTerminal (CostructuredArrow L ((L).obj P)) :=
      (CostructuredArrow.mkIdTerminal (S := L) (Y := P)).hasTerminal
    have : HasTerminal (CostructuredArrow L Q) := (CostructuredArrow.mapIso e).hasTerminal_iff.mp ht
    have : AB5OfSize.{u, u} V := AB5OfSize_of_univLE V
    infer_instance
  · have : IsEmpty (CostructuredArrow L Q) := not_nonempty_iff.mp h
    have : HasCoproducts.{0} V := fun I => (Colimits.LargeZariskiColimits.modules R).has_colimits_of_shape (Discrete I)
    have : AB4OfSize.{0} V := AB4OfSize_shrink.{0, u + 1} V
    have : HasExactColimitsOfShape (Discrete PEmpty.{1}) V := AB4OfSize.ofShape _
    exact HasExactColimitsOfShape.of_domain_equivalence V
      (equivalenceOfIsEmpty (Discrete PEmpty.{1}) (CostructuredArrow L Q))

instance lan_finiteLimits : PreservesFiniteLimits
    ((L).lan : (Y.Opensᵒᵖ ⥤ V) ⥤ X.Opensᵒᵖ ⥤ V) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
  intro T _ _
  apply preservesLimitsOfShape_of_evaluation ((L).lan : (Y.Opensᵒᵖ ⥤ V) ⥤ X.Opensᵒᵖ ⥤ V) T
  intro Q
  exact preservesLimitsOfShape_of_natIso (Large.OpenKanEvaluation.LargeOpenKanEvaluation.iso R L Q).symm

instance extension_finiteLimits : PreservesFiniteLimits
    (Functor.sheafPullbackConstruction.sheafPullback f.opensFunctor V J K) := by
  change PreservesFiniteLimits (sheafToPresheaf J V ⋙ (L).lan ⋙ presheafToSheaf K V)
  have : PreservesFiniteLimits ((L).lan ⋙ presheafToSheaf K V) := comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

instance restriction_preservesInjectives :
    (MixedCech.CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous f.opensFunctor V J K)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.OpenInjectives.LargeZariskiOpenInjectives
