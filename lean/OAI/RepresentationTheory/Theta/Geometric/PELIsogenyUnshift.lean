import OAI.RepresentationTheory.Theta.Geometric.PELIsogenyMarkingShift

/-! # PEL Isogeny Unshift -/

namespace OAI.RepresentationTheory.Theta.Geometric.PELIsogenyUnshift

noncomputable section

/-! Cancel one common scalar marking from an actual complementary
isogeny while retaining its literal abelian morphism. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u
variable {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}
    {P Q : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N S} {m : ℕ}

def unshiftPELIsogeny (a : (ZMod N)ˣ)
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (P.shiftMarking a) (Q.shiftMarking (a * a)) m) :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny P (Q.shiftMarking a) m where
  isogeny := e.isogeny
  dualHom := e.dualHom
  dualGroup := e.dualGroup
  poincare := e.poincare
  equivariant := e.equivariant
  polarization := e.polarization
  marking T z := by
    have h := (PELIsogenyMarkingShift.shiftPELIsogeny e a⁻¹).marking T z
    change (((P.shiftMarking a).shiftMarking a⁻¹).marking.hom.app (.op T) z).val ≫
      e.isogeny.hom = (((Q.shiftMarking (a * a)).shiftMarking a⁻¹).marking.hom.app (.op T) z).val at h
    change (((AlgebraicGeometry.AbelianScheme.TateComparison.Marking.levelScalarIso g N S a⁻¹ ≪≫ AlgebraicGeometry.AbelianScheme.TateComparison.Marking.levelScalarIso g N S a ≪≫ P.marking).hom.app (.op T)) z).val ≫
      e.isogeny.hom = (((AlgebraicGeometry.AbelianScheme.TateComparison.Marking.levelScalarIso g N S a⁻¹ ≪≫ AlgebraicGeometry.AbelianScheme.TateComparison.Marking.levelScalarIso g N S (a * a) ≪≫ Q.marking).hom.app (.op T)) z).val at h
    rw [← Iso.trans_assoc, ← AlgebraicGeometry.AbelianScheme.TateComparison.MarkingAction.levelScalarIso_mul, inv_mul_cancel, AlgebraicGeometry.AbelianScheme.TateComparison.MarkingAction.levelScalarIso_one,
      Iso.refl_trans, ← Iso.trans_assoc, ← AlgebraicGeometry.AbelianScheme.TateComparison.MarkingAction.levelScalarIso_mul, inv_mul_cancel_left] at h
    exact h

theorem unshiftPELIsogeny_hom (a : (ZMod N)ˣ)
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (P.shiftMarking a) (Q.shiftMarking (a * a)) m) :
    (unshiftPELIsogeny a e).isogeny.hom = e.isogeny.hom := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.PELIsogenyUnshift
