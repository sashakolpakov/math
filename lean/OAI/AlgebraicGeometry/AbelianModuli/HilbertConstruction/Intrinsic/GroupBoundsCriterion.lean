import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidalPullbackGraphBounds
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentedGroupGraphBounds

/-! # Group Bounds Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.GroupBoundsCriterion

noncomputable section

/-! Native group-operation bounds are exactly the two graph conditions in
the product presentations of the actual pulled-back family. This gives a
constructor for the existing bounded commutative-group operation data. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

local instance nativeCriterionProductFlat {S : Scheme.{u}} (X Y : Over S) [Flat X.hom] [Flat Y.hom] :
    Flat (X ⊗ Y).hom := inferInstanceAs (Flat (pullback.fst X.hom Y.hom ≫ X.hom))
local instance nativeCriterionProductFinitePresentation {S : Scheme.{u}} (X Y : Over S)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom] :
    LocallyOfFinitePresentation (X ⊗ Y).hom := inferInstanceAs
      (LocallyOfFinitePresentation (pullback.fst X.hom Y.hom ≫ X.hom))
local instance nativeCriterionPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [Flat X.hom] :
    Flat ((Over.pullback f).obj X).hom := inferInstanceAs (Flat (pullback.snd X.hom f))
local instance nativeCriterionPullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S)
    [LocallyOfFinitePresentation X.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj X).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom f))
local instance nativeCriterionPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [IsSeparated X.hom] :
    IsSeparated ((Over.pullback f).obj X).hom := inferInstanceAs (IsSeparated (pullback.snd X.hom f))

variable {S : Scheme.{u}} [IsNoetherian S] {X : Over S} [IsProper X.hom] [Smooth X.hom]
variable (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Pm Pi : Polynomial ℚ) (T : Over S)
variable (D : FamilyGroup.Operations.FamilyGroupOperations ((Over.pullback T.hom).obj X))

omit [AlgebraicGeometry.IsNoetherian S] in
theorem boundedNativeGroupOperations_property_iff :
    ((((FamilyOperationData.familyOperationDataEquiv X T).symm D).1.1 ∈
      (Bounded.EmbeddedMorphismFunctor.boundedEmbeddedMorphismSubfunctor ((P.product P).product P).embedding Pm).obj (Opposite.op T)) ∧
    (((FamilyOperationData.familyOperationDataEquiv X T).symm D).1.2 ∈
      (Bounded.EmbeddedMorphismFunctor.boundedEmbeddedMorphismSubfunctor (P.product P).embedding Pi).obj (Opposite.op T))) ↔
    D.ProjectiveGraphBounds (P.baseChange T.hom) Pm Pi := by
  change (Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom ((P.product P).product P).embedding) Pm
      ((Functor.Monoidal.μIso (Over.pullback T.hom) X X).inv ≫ D.mul) ∧
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial
      (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom (P.product P).embedding) Pi D.inv) ↔ _
  apply and_congr
  · exact ((P.product P).relativeProductGraph_hilbertPolynomial_iff P T.hom Pm
      ((Functor.Monoidal.μIso (Over.pullback T.hom) X X).inv ≫ D.mul)).trans
        (P.multiplicationGraph_changeProduct T.hom Pm D.mul).symm
  · exact P.relativeProductGraph_hilbertPolynomial_iff P T.hom Pi D.inv

def boundedNativeOperationsOfGraphBounds (hD : D.Laws)
    (hbound : D.ProjectiveGraphBounds (P.baseChange T.hom) Pm Pi) :
    Bounded.FamilyGroupPointClassification.BoundedCommutativeFamilyGroupOperations ((P.product P).product P).embedding
      (P.product P).embedding Pm Pi T :=
  ⟨⟨D, (boundedNativeGroupOperations_property_iff P Pm Pi T D).mpr hbound⟩, hD⟩

def boundedNativeGroupClassifierOfGraphBounds (hD : D.Laws)
    (hbound : D.ProjectiveGraphBounds (P.baseChange T.hom) Pm Pi) :
    T ⟶ Bounded.FamilyGroupParameter.boundedFamilyGroupParameter ((P.product P).product P).embedding
      (P.product P).embedding Pm Pi P.quasiProjective :=
  (Bounded.FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv ((P.product P).product P).embedding
    (P.product P).embedding Pm Pi P.quasiProjective T).symm
      (boundedNativeOperationsOfGraphBounds P Pm Pi T D hD hbound)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.GroupBoundsCriterion
