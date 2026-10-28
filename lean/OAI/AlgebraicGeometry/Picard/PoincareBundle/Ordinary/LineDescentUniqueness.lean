import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FaithfulPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantUniversal

/-! # Line Descent Uniqueness -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.LineDescentUniqueness

noncomputable section

/-!
# Uniqueness of the actual line bundle descended from ordinary geometric data
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [IsLocallyNoetherian Y] [Flat f] [Surjective f]
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
  (hD : Line.Bundles.IsLine (D.obj PUnit.unit))
  (N : Line.Bundles.LineBundle Y)
  (e : (Scheme.Modules.pullback f).obj N.sheaf ≅ D.obj PUnit.unit)
  (he : (Scheme.Modules.pullback (pullback.fst f f)).map e.hom ≫ (Geometric.CechInvariant.relationGluing f D).hom =
    (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
      pullback.condition).hom.app N.sheaf ≫ (Scheme.Modules.pullback (pullback.snd f f)).map e.hom)

include he in
/-- Every other recovery of the same ordinary line datum is uniquely isomorphic to its actual invariant. -/
theorem existsUnique_iso :
    ∃! a : N.sheaf ≅ (GlobalLineDescent.descendedLine f D hD).sheaf,
      (Scheme.Modules.pullback f).map a.hom ≫ (GlobalLineDescent.descendedLinePullbackIso f D hD).hom = e.hom := by
  obtain ⟨a, ha, hu⟩ := Cech.InvariantUniversal.existsUnique_lift f
    (pullback.fst f f) (pullback.snd f f) pullback.condition (D.obj PUnit.unit)
    (Geometric.CechInvariant.relationGluing f D) N.sheaf ⟨e.hom, he⟩
  have ha' : (Scheme.Modules.pullback f).map a ≫ Geometric.CechInvariant.ordinaryComparison f D = e.hom := ha
  have hc : IsIso (Geometric.CechInvariant.ordinaryComparison f D) := GlobalLineDescent.comparison_isIso f D hD
  have hcomp : IsIso ((Scheme.Modules.pullback f).map a ≫ Geometric.CechInvariant.ordinaryComparison f D) := by
    rw [ha']
    exact e.isIso_hom
  have hpull : IsIso ((Scheme.Modules.pullback f).map a) :=
    (@isIso_comp_right_iff _ _ _ _ _ _ _ hc).mp hcomp
  have hi : IsIso a := FaithfulPullback.isIso_of_pullback f a N.isLine
    (GlobalLineDescent.invariant_isLine f D hD) hpull
  refine ⟨@asIso _ _ _ _ a hi, ha', ?_⟩
  intro b hb
  apply Iso.ext
  exact hu b.hom hb

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.LineDescentUniqueness
