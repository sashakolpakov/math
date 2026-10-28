import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AmplePullbackFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GeometricFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Isomorphisms

/-! # Ample Pullback Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.AmplePullbackFiniteness

noncomputable section

/-! A proper relative morphism is finite when the pullback of a target line bundle is ample on every geometric fiber over the common base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem proper_overMap_isFinite_of_geometric_ample_pullback
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [IsProper f.left]
    [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom] (L : Line.Bundles.LineBundle Y.left)
    (hL : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      ((L.pullback f.left).pullback (Limits.pullback.fst X.hom s)).IsAmple) : IsFinite f.left := by
  apply GeometricFiniteness.proper_overMap_isFinite_of_geometric_baseChange f
  intro K _ _ s
  let g := ((Over.pullback s).map f).left
  let a := Limits.pullback.fst X.hom s
  let b := Limits.pullback.fst Y.hom s
  let p := ((Over.pullback s).obj Y).hom
  have H := Projective.PresentationBaseChange.overPullback_map_isPullback f s
  have : IsProper g := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : LocallyOfFiniteType p := inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd Y.hom s))
  have : IsSeparated p := inferInstanceAs (IsSeparated (Limits.pullback.snd Y.hom s))
  let e : ((L.pullback f.left).pullback a).sheaf ≅ ((L.pullback b).pullback g).sheaf :=
    (Scheme.Modules.pullbackComp a f.left).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr H.w).app L.sheaf ≪≫
        ((Scheme.Modules.pullbackComp g b).app L.sheaf).symm
  exact Proper.AmplePullbackFiniteness.proper_isFinite_of_ample_pullback g p (L.pullback b) ((hL K s).of_iso e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.AmplePullbackFiniteness
