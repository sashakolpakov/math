import OAI.RepresentationTheory.Theta.Geometric.Reference.LieSignature
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Distinct Fiber PEL Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.DistinctFiberPELComparison

noncomputable section

section

/-! An isomorphism of the original polarized fibers with their actual
integral actions gives an isomorphism of the literal PEL pullbacks. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli

def pelFiberIsoOfPolarized {R : Type} [CommRing R] {S : Scheme} {g N : ℕ}
    (A : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N S) {δ : Fin g → ℕ} {c : R →+* R} (hA : A.IsPEL δ c)
    {T : Scheme} (x y : T ⟶ S)
    (e : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((A.toPolarized hA).pullback x) ((A.toPolarized hA).pullback y))
    (ha : ∀ a, ((AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd A.action).pullback x).map a ≫ e.abelian.hom =
      e.abelian.hom ≫ ((AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd A.action).pullback y).map a) :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (A.pullback x) (A.pullback y) where
  abelian := e.abelian
  dual := e.dual
  abelianGroup := e.abelianGroup
  dualGroup := e.dualGroup
  polarization := e.polarization
  poincare := e.poincare
  marking := e.level
  equivariant a := by
    change (AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd ((AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endBaseChange A.abelian.scheme x).comp A.action)).map a ≫ e.abelian.hom =
      e.abelian.hom ≫ (AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd ((AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endBaseChange A.abelian.scheme y).comp A.action)).map a
    rw [Reference.LieSignature.actionFromEnd_baseChange, Reference.LieSignature.actionFromEnd_baseChange]
    exact ha a

end

/-! Original polarized full-level comparisons across two actual
families give isomorphisms of their literal PEL pullbacks. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli

def pelFiberIsoOfPolarizedBetween {R : Type} [CommRing R] {S T : Scheme} {g N : ℕ}
    (A : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N S) (B : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N T)
    {δ : Fin g → ℕ} {c : R →+* R} (hA : A.IsPEL δ c) (hB : B.IsPEL δ c)
    {U : Scheme} (x : U ⟶ S) (y : U ⟶ T)
    (e : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso ((A.toPolarized hA).pullback x) ((B.toPolarized hB).pullback y))
    (ha : ∀ a, ((AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd A.action).pullback x).map a ≫ e.abelian.hom =
      e.abelian.hom ≫ ((AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd B.action).pullback y).map a) :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (A.pullback x) (B.pullback y) where
  abelian := e.abelian
  dual := e.dual
  abelianGroup := e.abelianGroup
  dualGroup := e.dualGroup
  polarization := e.polarization
  poincare := e.poincare
  marking := e.level
  equivariant a := by
    change (AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd ((AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endBaseChange A.abelian.scheme x).comp A.action)).map a ≫ e.abelian.hom =
      e.abelian.hom ≫ (AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd ((AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endBaseChange B.abelian.scheme y).comp B.action)).map a
    rw [Reference.LieSignature.actionFromEnd_baseChange, Reference.LieSignature.actionFromEnd_baseChange]
    exact ha a

end

end OAI.RepresentationTheory.Theta.Geometric.DistinctFiberPELComparison
