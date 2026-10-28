import OAI.RepresentationTheory.Theta.Geometric.Reference.LieSignature

/-! # PEL Action Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.PELActionPullback

noncomputable section

/-! Actual base-changed PEL endomorphisms equal the pulled-back
integral-action maps of the same family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem pelAction_pullback_schemeMap {R : Type} [CommRing R] {S T : Scheme} {g N : ℕ}
    (A : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N S) (x : T ⟶ S) (a : R) :
    AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap (A.pullback x).abelian.scheme ((A.pullback x).action a) =
      ((AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd A.action).pullback x).map a :=
  AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap A.abelian.scheme x (A.action a)

end

end OAI.RepresentationTheory.Theta.Geometric.PELActionPullback
