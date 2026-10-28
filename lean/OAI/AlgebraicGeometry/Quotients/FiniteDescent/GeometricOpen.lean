import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricDense
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Geometric Open -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricOpen

noncomputable section

/-! A nonempty open of a geometrically integral scheme over a field is
geometrically integral. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.GeometricOpenSubset

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
variable (U : X.Opens) [Nonempty U]

theorem geometricallyIntegral : GeometricallyIntegral (U.ι ≫ f) := by
  constructor
  intro L _ t Y p q h
  have : Surjective t := ⟨fun z => ⟨default, Subsingleton.elim _ z⟩⟩
  have : Surjective p := MorphismProperty.of_isPullback h.flip ‹Surjective t›
  have : Nonempty Y := by
    obtain ⟨y, _⟩ := p.surjective (Classical.choice (inferInstance : Nonempty U))
    exact ⟨y⟩
  have : IsIntegral (pullback f t) := GeometricallyIntegral.geometrically_isIntegral
    t (pullback.fst f t) (pullback.snd f t) (IsPullback.of_hasPullback f t)
  let i : Y ⟶ pullback f t := pullback.lift (p ≫ U.ι) q (by simpa only [Category.assoc] using h.w)
  have ho : IsPullback p (i ≫ pullback.snd f t) (U.ι ≫ f) t := by
    simpa only [i, pullback.lift_snd] using h
  have hi : IsPullback p i U.ι (pullback.fst f t) :=
    IsPullback.of_bot ho (by simp only [i, pullback.lift_fst]) (IsPullback.of_hasPullback f t)
  have : IsOpenImmersion i := MorphismProperty.of_isPullback hi inferInstance
  exact isIntegral_of_isOpenImmersion i

end Construction.GeometricOpenSubset

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricOpen
