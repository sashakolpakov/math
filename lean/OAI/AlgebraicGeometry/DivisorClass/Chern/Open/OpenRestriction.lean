import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition

/-! # Open Restriction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: restriction of actual algebraic line bundles to open subschemes

The restricted local trivializations are obtained using the genuine restriction
functors and their composition isomorphisms. In particular this restricts a
line bundle to each actual integral component of a smooth projective scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Open.OpenRestriction.Construction

/-- Pull a genuine local frame back along an open immersion. -/
def restrictFrameAlongOpen {X Y : Scheme} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (U : X.Opens) (e : M.restrict U.ι ≅ Line.Bundles.Construction.structureModule U.toScheme) :
    (M.restrict f).restrict (f ⁻¹ᵁ U).ι ≅ Line.Bundles.Construction.structureModule (f ⁻¹ᵁ U).toScheme :=
  ((Scheme.Modules.restrictFunctorComp (f ⁻¹ᵁ U).ι f).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (morphismRestrict_ι f U).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (f ∣_ U) U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (f ∣_ U)).mapIso e ≪≫ Scheme.Modules.restrictUnitIso (f ∣_ U)

end Open.OpenRestriction.Construction

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)

/-- Restriction of the actual module sheaf, with its induced rank-one local frames. -/
def Line.Bundles.AlgebraicLineBundle.restrictToOpen (Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (f : Y.carrier ⟶ X.carrier)
    [IsOpenImmersion f] : Line.Bundles.AlgebraicLineBundle Y where
  sheaf := L.sheaf.restrict f
  locallyTrivial y := ⟨f ⁻¹ᵁ L.trivializingOpen (f y), L.mem_trivializingOpen (f y),
    ⟨Open.OpenRestriction.Construction.restrictFrameAlongOpen f L.sheaf (L.trivializingOpen (f y)) (L.trivialization (f y))⟩⟩

/-- The actual line bundle on an integral component of the original scheme. -/
def Line.Bundles.AlgebraicLineBundle.componentLineBundle (C : irreducibleComponents X.carrier) :
    Line.Bundles.AlgebraicLineBundle (X.componentVariety C).presentation :=
  L.restrictToOpen (X.componentVariety C).presentation (X.componentInclusion C)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
