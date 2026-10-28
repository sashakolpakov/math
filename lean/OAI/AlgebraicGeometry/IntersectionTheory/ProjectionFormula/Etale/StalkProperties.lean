import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Stalk Properties -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.StalkProperties

noncomputable section

/-! An actual etale open neighborhood gives flatness, formal
unramifiedness, and essential finite type for the original stalk map. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem of_open {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens)
    [Etale (U.ι ≫ f)] (x : X) (hx : x ∈ U) :
    (f.stalkMap x).hom.Flat ∧ (f.stalkMap x).hom.FormallyUnramified ∧
      (f.stalkMap x).hom.EssFiniteType := by
  let y : U := ⟨x, hx⟩
  have hflat := Flat.stalkMap (U.ι ≫ f) y
  have hun := FormallyUnramified.stalkMap (U.ι ≫ f) y
  have hft := LocallyOfFiniteType.stalkMap (U.ι ≫ f) y
  rw [Scheme.Hom.stalkMap_comp] at hflat hun hft
  exact ⟨(RingHom.Flat.respectsIso.cancel_right_isIso (f.stalkMap x) (U.ι.stalkMap y)).mp hflat,
    (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso (f.stalkMap x) (U.ι.stalkMap y)).mp hun,
    (RingHom.EssFiniteType.respectsIso.cancel_right_isIso (f.stalkMap x) (U.ι.stalkMap y)).mp hft⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.StalkProperties
