import OAI.RepresentationTheory.Theta.Geometric.PELIsogenyUnshift
import OAI.RepresentationTheory.Theta.Geometric.PELFrameTransport
import OAI.RepresentationTheory.Theta.Geometric.PowerTatePreimages

/-! # Unshift PEL Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.UnshiftPELTransport

noncomputable section

/-! Cancelling scalar markings commutes with the actual Tate-frame
transport through complete source and target PEL isomorphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
variable {R : Type} [CommRing R] {g N s q m : ℕ} [Fact q.Prime]
    {S : Scheme} (T : Over S) {P Q Y Z : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N S}

theorem pelFrameTransport_refl (frame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s P.abelian.scheme T q) :
    (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl P).transportFrame T frame = frame := by
  ext z v i
  change frame (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := T) (q := q) (𝟙 P.abelian.scheme) z) v i = frame z v i
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.Functor.rationalTateMap_id]
  rfl

theorem pelFrameTransport_sourceIntegral (j : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso P Q)
    (frame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s Q.abelian.scheme T q) (v : Fin s × Bool) :
    PowerTatePreimages.framedSourceIntegral (j.transportFrame T frame) v = PowerTatePreimages.framedSourceIntegral frame v := by
  rw [PowerTatePreimages.framedSourceIntegral, PowerTatePreimages.framedSourceIntegral, PELFrameTransport.pelFrameTransport_integral]

variable (a : (ZMod N)ˣ) (f : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny Y (P.shiftMarking (a * a)) m)
    (j : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (Q.shiftMarking a) Y) (k : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (P.shiftMarking a) Z)

theorem unshiftFrame_equivariant (χ : Fin s × Bool → R →+* ℤ_[q])
    (frame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s Y.abelian.scheme T q) (hf : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame Y T q χ frame) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame Q T q χ (j.transportFrame T frame) := by
  simpa only [AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame, AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData.shiftMarking] using j.transportFrame_equivariant T χ frame hf

def unshiftTransport : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny Q Z m :=
  (PELIsogenyUnshift.unshiftPELIsogeny a (f.transport j (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl _))).transport (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl Q) k

theorem unshiftTransport_framedLattice
    (frame : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateFrame s Y.abelian.scheme T q) (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice (j.transportFrame T frame) (unshiftTransport a f j k).isogeny.hom v =
      AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame f.isogeny.hom v := by
  let f₁ := PELIsogenyUnshift.unshiftPELIsogeny a (f.transport j (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl _))
  have H := PELFrameTransport.pelIsogeny_transport_framed_lattice T f₁ (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl Q) k
    (j.transportFrame T frame) v
  rw [pelFrameTransport_refl] at H
  change AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice (j.transportFrame T frame) (unshiftTransport a f j k).isogeny.hom v = _ at H
  exact H.trans (PELFrameTransport.pelIsogeny_transport_framed_lattice T f j (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl _) frame v)

end

end OAI.RepresentationTheory.Theta.Geometric.UnshiftPELTransport
