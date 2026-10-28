import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.SheafExactness
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatModuleKanExtension
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Injectives -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Injectives.CrystallineOpenInjectives

noncomputable section

/-!
# Open restriction preserves injective crystalline sheaves

The comma category computing extension by zero is empty outside the open
subscheme, and has a terminal object inside it. Its module colimits are
therefore exact. The sheafified left adjoint is exact, so restriction
preserves injectives and may be applied to native injective resolutions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X Y : Over (Spec (CommRingCat.of k))} (j : X ⟶ Y) [IsOpenImmersion j.left]

local notation "Inclusion" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Embedding.CrystallineOpenEmbedding.functor p k j
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "SmallTopology" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "LargeTopology" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k Y

instance comma_exactColimits (Q : (Site.Object p k Y)ᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (Inclusion).op Q) V := by
  classical
  by_cases h : Nonempty (CostructuredArrow (Inclusion).op Q)
  · obtain ⟨T⟩ := h
    obtain ⟨P, e⟩ := Topology.CrystallineOpenTopology.downwardsClosed p k j T.hom.unop
    have ht : HasTerminal (CostructuredArrow (Inclusion).op (op ((Inclusion).obj P))) :=
      (CostructuredArrow.mkIdTerminal (S := (Inclusion).op) (Y := op P)).hasTerminal
    have : HasTerminal (CostructuredArrow (Inclusion).op Q) :=
      (CostructuredArrow.mapIso e.op.symm).hasTerminal_iff.mp ht
    have : AB5OfSize.{u, u + 1} V := AB5OfSize_of_univLE V
    infer_instance
  · have : IsEmpty (CostructuredArrow (Inclusion).op Q) := not_nonempty_iff.mp h
    exact HasExactColimitsOfShape.of_domain_equivalence V
      (equivalenceOfIsEmpty (Discrete PEmpty.{1}) (CostructuredArrow (Inclusion).op Q))

instance lan_finiteLimits : PreservesFiniteLimits
    ((Inclusion).op.lan : ((Site.Object p k X)ᵒᵖ ⥤ V) ⥤
      (Site.Object p k Y)ᵒᵖ ⥤ V) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
  intro T _ _
  apply preservesLimitsOfShape_of_evaluation
    ((Inclusion).op.lan : ((Site.Object p k X)ᵒᵖ ⥤ V) ⥤
      (Site.Object p k Y)ᵒᵖ ⥤ V) T
  intro Q
  exact preservesLimitsOfShape_of_natIso
    (NumberTheory.PadicHodge.IntegralComparison.FlatModuleKanExtension.evaluationIso
      (Site.CoefficientRing p k) (Inclusion).op Q).symm

instance sheafLeftAdjoint_finiteLimits : PreservesFiniteLimits
    (Functor.sheafPullbackConstruction.sheafPullback Inclusion V SmallTopology LargeTopology) := by
  change PreservesFiniteLimits
    (sheafToPresheaf SmallTopology V ⋙ (Inclusion).op.lan ⋙ presheafToSheaf LargeTopology V)
  have : PreservesFiniteLimits ((Inclusion).op.lan ⋙ presheafToSheaf LargeTopology V) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

instance restriction_preservesInjectives :
    (SheafExactness.CrystallineOpenSheafExactness.restriction p k j).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous Inclusion V SmallTopology LargeTopology)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineOpen.Injectives.CrystallineOpenInjectives
