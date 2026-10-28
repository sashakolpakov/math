import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PointAffine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ContractedAmpleFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.GeometricFiberFiniteness

/-! # Ample Pullback Finite General -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AmplePullbackFiniteGeneral

noncomputable section

/-! A proper morphism of arbitrary schemes is finite if the pullback of a target line bundle is ample. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem proper_isFinite_of_ample_pullback_general
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (L : Line.Bundles.LineBundle Y)
    (hL : (L.pullback f).IsAmple) : IsFinite f := by
  apply GeometricFiberFiniteness.proper_isFinite_of_geometric_fieldPullbacks f
  intro K _ _ a
  have : IsAffineHom a := Field.PointAffine.fieldPoint_isAffineHom a
  have : IsAffineHom (pullback.fst f a) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f a).flip (inferInstance : IsAffineHom a)
  let p := pullback.snd f a
  have : IsProper p := inferInstanceAs (IsProper (pullback.snd f a))
  have : CompactSpace (pullback f a : Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian (pullback f a) := { __ := LocallyOfFiniteType.isLocallyNoetherian p }
  have : Finite (pullback f a : Scheme.{u}) :=
    ContractedAmpleFiniteness.contracted_ample_noetherian_finite p f (pullback.fst f a) a pullback.condition L hL
  have : LocallyQuasiFinite p := LocallyQuasiFinite.of_finite_preimage_singleton p (fun _ => Set.toFinite _)
  exact IsFinite.of_locallyQuasiFinite p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AmplePullbackFiniteGeneral
