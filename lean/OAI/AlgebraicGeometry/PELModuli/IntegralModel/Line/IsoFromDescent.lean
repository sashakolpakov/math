import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OrdinaryLineBundleRecovery
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.LineDescentUniqueness

/-! # Iso From Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Line.IsoFromDescent

noncomputable section

/-! An isomorphism of the complete ordinary descent data determines
an actual isomorphism of the quotient line bundles. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

theorem ordinaryLineDatumIso_compatible {X Y : Scheme.{0}} (f : X ⟶ Y)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f)) (M : Y.Modules)
    (e : Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f M ≅ D) :
    (Scheme.Modules.pullback (pullback.fst f f)).map
        (Picard.PoincareBundle.DescentComponentIsomorphisms.componentIso Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f e).hom ≫
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f D).hom =
    (Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
      pullback.condition).hom.app M ≫
        (Scheme.Modules.pullback (pullback.snd f f)).map
          (Picard.PoincareBundle.DescentComponentIsomorphisms.componentIso Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f e).hom := by
  have h := e.hom.comm (pullback.snd f f ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
    (pullback.fst f f) (pullback.snd f f) pullback.condition rfl
  change (Scheme.Modules.pullback (pullback.fst f f)).map
      (Picard.PoincareBundle.DescentComponentIsomorphisms.componentIso Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f e).hom ≫
    (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f D).hom =
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f (Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f M)).hom ≫
        (Scheme.Modules.pullback (pullback.snd f f)).map
          (Picard.PoincareBundle.DescentComponentIsomorphisms.componentIso Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f e).hom at h
  rw [Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum_gluing] at h
  exact h

theorem lineIso_of_ordinaryDescentIso {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e : Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f L.sheaf ≅ Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f M.sheaf) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  let D := Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f M.sheaf
  have hD : Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit) := (M.pullback f).locallyTrivial
  let eL := Picard.PoincareBundle.DescentComponentIsomorphisms.componentIso Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f e
  let eM := Picard.PoincareBundle.DescentComponentIsomorphisms.componentIso Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f (CategoryTheory.Iso.refl D)
  obtain ⟨a, _, _⟩ := Picard.PoincareBundle.Ordinary.LineDescentUniqueness.existsUnique_iso f D hD
    (⟨L.sheaf, L.locallyTrivial⟩ : Picard.PoincareBundle.Line.Bundles.LineBundle Y) eL
    (ordinaryLineDatumIso_compatible f D L.sheaf e)
  obtain ⟨c, _, _⟩ := Picard.PoincareBundle.Ordinary.LineDescentUniqueness.existsUnique_iso f D hD
    (⟨M.sheaf, M.locallyTrivial⟩ : Picard.PoincareBundle.Line.Bundles.LineBundle Y) eM
    (ordinaryLineDatumIso_compatible f D M.sheaf (CategoryTheory.Iso.refl D))
  exact ⟨a ≪≫ c.symm⟩

theorem lineIso_of_ordinaryRecoveries {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (eL : (L.pullback f).sheaf ≅ D.obj PUnit.unit)
    (eM : (M.pullback f).sheaf ≅ D.obj PUnit.unit)
    (hL : (Scheme.Modules.pullback (pullback.fst f f)).map eL.hom ≫
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f D).hom =
        (Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
          pullback.condition).hom.app L.sheaf ≫ (Scheme.Modules.pullback (pullback.snd f f)).map eL.hom)
    (hM : (Scheme.Modules.pullback (pullback.fst f f)).map eM.hom ≫
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f D).hom =
        (Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
          pullback.condition).hom.app M.sheaf ≫ (Scheme.Modules.pullback (pullback.snd f f)).map eM.hom) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  have hD : Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit) :=
    Picard.PoincareBundle.Line.Bundles.IsLine.of_iso (L.pullback f).locallyTrivial eL
  obtain ⟨a, _, _⟩ := Picard.PoincareBundle.Ordinary.LineDescentUniqueness.existsUnique_iso f D hD
    (⟨L.sheaf, L.locallyTrivial⟩ : Picard.PoincareBundle.Line.Bundles.LineBundle Y) eL hL
  obtain ⟨b, _, _⟩ := Picard.PoincareBundle.Ordinary.LineDescentUniqueness.existsUnique_iso f D hD
    (⟨M.sheaf, M.locallyTrivial⟩ : Picard.PoincareBundle.Line.Bundles.LineBundle Y) eM hM
  exact ⟨a ≪≫ b.symm⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Line.IsoFromDescent
