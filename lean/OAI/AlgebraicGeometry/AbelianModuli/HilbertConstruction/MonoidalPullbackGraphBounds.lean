import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GraphBundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.ProductGraphEmbeddingComparison

/-! # Monoidal Pullback Graph Bounds -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The monoidal pullback product isomorphism preserves the embedding
bundle and the actual multiplication-graph Hilbert condition. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def Projective.ProjectivePresentations.ProjectivePresentation.monoidalBaseChangeTwistingIso
    {S T : Scheme.{u}} {X Y : Over S} (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Q : Projective.ProjectivePresentations.ProjectivePresentation Y) (f : T ⟶ S) :
    (((P.product Q).baseChange f).ampleLineBundle.pullback
      (Functor.Monoidal.μIso (Over.pullback f) X Y).hom.left).sheaf ≅
      ((P.baseChange f).product (Q.baseChange f)).ampleLineBundle.sheaf :=
  (Scheme.Modules.pullback (Functor.Monoidal.μIso (Over.pullback f) X Y).hom.left).mapIso
      ((P.product Q).baseChangeTwistingBundleIso f) ≪≫
    (Scheme.Modules.pullbackComp (Functor.Monoidal.μIso (Over.pullback f) X Y).hom.left
      (pullback.fst (X ⊗ Y).hom f)).app (P.product Q).ampleLineBundle.sheaf ≪≫
        (P.productBaseChangeTwistingBundleIso Q f).symm

local instance MonoidalPullbackGraphBounds.monoidalBoundProductFlat {S : Scheme.{u}} (X Y : Over S) [Flat X.hom] [Flat Y.hom] :
    Flat (X ⊗ Y).hom := inferInstanceAs (Flat (pullback.fst X.hom Y.hom ≫ X.hom))
local instance MonoidalPullbackGraphBounds.monoidalBoundProductFinitePresentation {S : Scheme.{u}} (X Y : Over S)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom] :
    LocallyOfFinitePresentation (X ⊗ Y).hom := inferInstanceAs
      (LocallyOfFinitePresentation (pullback.fst X.hom Y.hom ≫ X.hom))
local instance MonoidalPullbackGraphBounds.monoidalBoundPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [Flat X.hom] :
    Flat ((Over.pullback f).obj X).hom := inferInstanceAs (Flat (pullback.snd X.hom f))
local instance MonoidalPullbackGraphBounds.monoidalBoundPullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S)
    [LocallyOfFinitePresentation X.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj X).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom f))
local instance MonoidalPullbackGraphBounds.monoidalBoundPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [IsSeparated X.hom] :
    IsSeparated ((Over.pullback f).obj X).hom := inferInstanceAs (IsSeparated (pullback.snd X.hom f))

theorem Projective.ProjectivePresentations.ProjectivePresentation.multiplicationGraph_changeProduct
    {S T : Scheme.{u}} {X : Over S} [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated X.hom]
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (f : T ⟶ S) (R : Polynomial ℚ)
    (p : (Over.pullback f).obj X ⊗ (Over.pullback f).obj X ⟶ (Over.pullback f).obj X) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial
      (((P.baseChange f).product (P.baseChange f)).product (P.baseChange f)).embedding R p ↔
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (((P.product P).baseChange f).product (P.baseChange f)).embedding R
      ((Functor.Monoidal.μIso (Over.pullback f) X X).inv ≫ p) := by
  let Y := (Over.pullback f).obj X
  let Q := P.baseChange f
  let c := Functor.Monoidal.μIso (Over.pullback f) X X
  let ei : (Q.ampleLineBundle.pullback (Iso.refl Y).hom.left).sheaf ≅ Q.ampleLineBundle.sheaf :=
    (Scheme.Modules.pullbackId Y.left).app Q.ampleLineBundle.sheaf
  have h := (Q.product Q).graphHilbertPolynomial_transport_of_bundleIso Q
    ((P.product P).baseChange f) Q c (Iso.refl Y) (P.monoidalBaseChangeTwistingIso P f) ei R p
  change Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial ((Q.product Q).product Q).embedding R p ↔
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (((P.product P).baseChange f).product Q).embedding R
      (c.inv ≫ p ≫ 𝟙 Y) at h
  rw [Category.comp_id] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
