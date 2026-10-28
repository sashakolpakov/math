import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Unramified Open Factor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnramifiedOpenFactor

noncomputable section

/-! A factor of an open immersion through an unramified morphism
of finite type is again an open immersion. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem factor {X Y S : Scheme} (f : X ⟶ Y) (g : Y ⟶ S)
    [FormallyUnramified g] [LocallyOfFiniteType g] [IsOpenImmersion (f ≫ g)] :
    IsOpenImmersion f := by
  let gr : X ⟶ pullback (f ≫ g) g := pullback.lift (𝟙 X) f (by simp)
  have hgr : IsOpenImmersion gr :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (pullback_lift_diagonal_isPullback f g) inferInstance
  let := hgr
  have hsnd : IsOpenImmersion (pullback.snd (f ≫ g) g) :=
    MorphismProperty.pullback_snd (P := @IsOpenImmersion) _ _ inferInstance
  let := hsnd
  have he : f = gr ≫ pullback.snd (f ≫ g) g := by simp [gr]
  rw [he]
  infer_instance

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnramifiedOpenFactor
