import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Ample
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AmplePullbackIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineTrivializationOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricPointsOf

/-! # Proper Ample -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperAmple.Construction.ProperAmplePullback

noncomputable section

/-! A proper morphism with an ample pulled-back line bundle is finite. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (hL : (L.pullback f).IsAmple) : IsFinite f := by
  have : LocallyQuasiFinite f := by
    apply GeometricPointsOf.Construction.GeometricPoints.locallyQuasiFinite_of_finite_geometric_points
    intro K hK hclosed a
    let P : Over (Spec (.of K)) := Over.mk (pullback.snd f a)
    let q : P.left ⟶ X := pullback.fst f a
    have : IsProper P.hom := by dsimp [P]; infer_instance
    have : IsAffineHom a := LineTrivializationOf.Construction.LineTrivialization.isAffineHom_from_field a
    have : IsAffineHom q := MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback f a).flip (inferInstance : IsAffineHom a)
    obtain ⟨e⟩ := LineTrivializationOf.Construction.LineTrivialization.pullback_trivial_over_field a L
    let eP : ((L.pullback f).pullback q).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left :=
      (Scheme.Modules.pullbackComp q f).app L.sheaf ≪≫
        (Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := a))).app L.sheaf ≪≫
        (Scheme.Modules.pullbackComp P.hom a).symm.app L.sheaf ≪≫
        (Scheme.Modules.pullback P.hom).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso P.hom
    have : IsFinite P.hom := Ample.Construction.AmpleFinite.of_trivial P ((L.pullback f).pullback q)
      (AmplePullbackIs.Construction.AmplePullback.isAmple q (L.pullback f) hL) eP
    have hf := P.hom.finite_preimage (Set.toFinite (Set.univ : Set (Spec (.of K))))
    have : Finite P.left := Set.finite_univ_iff.mp (by
      simpa only [Set.preimage_univ] using hf)
    have : Finite {p : Spec (.of K) ⟶ P.left // p ≫ P.hom = 𝟙 _} :=
      Finite.of_equiv _ (pointEquivClosedPoint P.hom).symm
    let ep : (Over.mk a ⟶ Over.mk f) ≃
        {p : Spec (.of K) ⟶ P.left // p ≫ P.hom = 𝟙 _} :=
      PowerOrbitEq.Construction.PowerOrbit.fieldPointPullbackEquiv (Over.mk f) a
    exact Finite.of_equiv _ ep.symm
  exact AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite f

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperAmple.Construction.ProperAmplePullback
