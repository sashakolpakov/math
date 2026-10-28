import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingAction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies

/-! # PEL Isogeny Marking Shift -/

namespace OAI.RepresentationTheory.Theta.Geometric.PELIsogenyMarkingShift

noncomputable section

/-! Simultaneous scalar changes of full markings preserve actual PEL isogenies. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}
    {P Q : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N S} {n : ℕ}

def shiftPELIsogeny (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny P Q n) (a : (ZMod N)ˣ) :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (P.shiftMarking a) (Q.shiftMarking a) n where
  isogeny := e.isogeny
  dualHom := e.dualHom
  dualGroup := e.dualGroup
  poincare := e.poincare
  equivariant := e.equivariant
  polarization := e.polarization
  marking T z := e.marking T ((AlgebraicGeometry.AbelianScheme.TateComparison.Marking.levelScalarIso g N S a).hom.app (.op T) z)

theorem shiftPELIsogeny_hom (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny P Q n) (a : (ZMod N)ˣ) :
    (shiftPELIsogeny e a).isogeny.hom = e.isogeny.hom := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.PELIsogenyMarkingShift
