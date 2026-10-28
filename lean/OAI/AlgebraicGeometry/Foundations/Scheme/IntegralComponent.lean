import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Integral Component -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme

noncomputable section

/-!
# The component of an integral projective variety

The genuine component inclusion of an integral variety is an isomorphism
over its specified complex base. This records the geometric identification
needed for the converse direction of the componentwise conjecture reduction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (V : IntegralProjective.IntegralProjectiveVariety)

/-- The whole integral variety, as an actual irreducible component. -/
def IntegralProjective.IntegralProjectiveVariety.wholeComponent : irreducibleComponents V.carrier :=
  ⟨Set.univ, by simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]⟩

@[simp]
theorem IntegralProjective.IntegralProjectiveVariety.wholeComponent_val : V.wholeComponent.val = Set.univ := rfl

/-- There are no other irreducible components of an integral variety. -/
theorem IntegralProjective.IntegralProjectiveVariety.component_val_eq_univ (C : irreducibleComponents V.carrier) :
    C.val = Set.univ := by
  simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using C.property

theorem IntegralProjective.IntegralProjectiveVariety.component_eq_wholeComponent (C : irreducibleComponents V.carrier) :
    C = V.wholeComponent :=
  Subtype.ext (V.component_val_eq_univ C)

/-- The actual component inclusion is surjective in this integral case. -/
theorem IntegralProjective.IntegralProjectiveVariety.componentInclusion_surjective (C : irreducibleComponents V.carrier) :
    Function.Surjective (V.presentation.componentInclusion C) :=
  Set.range_eq_univ.mp
    ((V.presentation.componentInclusion_range C).trans (V.component_val_eq_univ C))

/-- Hence the actual open component inclusion is an isomorphism of schemes. -/
instance IntegralProjective.IntegralProjectiveVariety.componentInclusion_isIso (C : irreducibleComponents V.carrier) :
    IsIso (V.presentation.componentInclusion C) :=
  (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨inferInstance, (surjective_iff _).mpr (V.componentInclusion_surjective C)⟩

/-- The component identification preserves the given complex base map. -/
def IntegralProjective.IntegralProjectiveVariety.componentOverIso (C : irreducibleComponents V.carrier) :
    (V.presentation.componentVariety C).toOver ≅ V.toOver := by
  let e : (V.presentation.componentVariety C).carrier ≅ V.carrier :=
    @asIso _ _ _ _ (V.presentation.componentInclusion C) (V.componentInclusion_isIso C)
  exact Over.isoMk e
    (V.presentation.componentInclusion_over C)

@[simp]
theorem IntegralProjective.IntegralProjectiveVariety.componentOverIso_hom_left (C : irreducibleComponents V.carrier) :
    (V.componentOverIso C).hom.left = V.presentation.componentInclusion C := rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme
