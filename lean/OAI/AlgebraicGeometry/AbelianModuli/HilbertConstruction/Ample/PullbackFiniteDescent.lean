import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AmplePullbackFiniteGeneral
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiniteSurjectiveDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Isomorphisms

/-! # Pullback Finite Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PullbackFiniteDescent

noncomputable section

/-! A proper morphism is finite if a target line bundle has ample pullback after a surjective base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem proper_isFinite_of_ample_pullback_after_surjective_baseChange
    {X Y Z P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (H : IsPullback a b f g) [IsProper f] [Surjective g] (L : Line.Bundles.LineBundle Y)
    (hL : ((L.pullback f).pullback a).IsAmple) : IsFinite f := by
  have : IsProper b := MorphismProperty.of_isPullback H (inferInstance : IsProper f)
  let e : ((L.pullback f).pullback a).sheaf ≅ ((L.pullback g).pullback b).sheaf :=
    (Scheme.Modules.pullbackComp a f).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr H.w).app L.sheaf ≪≫
        ((Scheme.Modules.pullbackComp b g).app L.sheaf).symm
  have : IsFinite b := Proper.AmplePullbackFiniteGeneral.proper_isFinite_of_ample_pullback_general b (L.pullback g) (hL.of_iso e)
  exact Proper.FiniteSurjectiveDescent.proper_isFinite_of_surjective_baseChange H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PullbackFiniteDescent
