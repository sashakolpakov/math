import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

/-! # Ambient Projections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientProjections

noncomputable section

/-! The native Hilbert ambient pullback map preserves both product projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X : Over S) {T U : Over S} (a : T ⟶ U)

@[reassoc]
theorem ambientMap_projection : Functor.ambientMap X a ≫ Functor.ambientProjection X U =
    Functor.ambientProjection X T ≫ a.left := (Functor.ambient_isPullback X a).w.symm

@[reassoc]
theorem ambientMap_second : Functor.ambientMap X a ≫ (prod.snd : U ⨯ X ⟶ X).left =
    (prod.snd : T ⨯ X ⟶ X).left := by
  change (prod.map a (𝟙 X)).left ≫ (prod.snd : U ⨯ X ⟶ X).left = _
  rw [← Over.comp_left, prod.map_snd, Category.comp_id]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientProjections
