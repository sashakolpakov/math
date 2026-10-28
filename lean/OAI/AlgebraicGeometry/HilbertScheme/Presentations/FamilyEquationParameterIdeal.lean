import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FamilyEquationUniversalIdeal

/-! # Family Equation Parameter Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-! Pull arbitrary natural family equations to a parameter scheme and
identify their solution condition with actual ideal-sheaf vanishing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {M T : Over S}

def Endomorphisms.Core.FamilyMorphismEquation.parameterIdeal (r : Endomorphisms.Core.FamilyMorphismEquation F) (φ : yoneda.obj M ⟶ F) :
    (M ⨯ r.source).left.IdealSheafData := (r.comap φ).universalIdeal

theorem Endomorphisms.Core.FamilyMorphismEquation.parameterIdeal_comap_eq_bot_iff
    (r : Endomorphisms.Core.FamilyMorphismEquation F) (φ : yoneda.obj M ⟶ F) (x : T ⟶ M) :
    (r.parameterIdeal φ).comap (prod.map x (𝟙 r.source)).left = ⊥ ↔
      r.lhs.app (.op T) (φ.app (.op T) x) = r.rhs.app (.op T) (φ.app (.op T) x) :=
  (r.comap φ).universalIdeal_comap_eq_bot_iff x

theorem FamilyEquationParameterIdeal.Core.satisfiesEquations_iff_parameterIdeals
    (R : List (Endomorphisms.Core.FamilyMorphismEquation F)) (φ : yoneda.obj M ⟶ F) (x : T ⟶ M) :
    Endomorphisms.Core.SatisfiesEquations R (φ.app (.op T) x) ↔ ∀ r ∈ R,
      (r.parameterIdeal φ).comap (prod.map x (𝟙 r.source)).left = ⊥ := by
  constructor
  · intro h r hr
    exact (r.parameterIdeal_comap_eq_bot_iff φ x).mpr (h r hr)
  · intro h r hr
    exact (r.parameterIdeal_comap_eq_bot_iff φ x).mp (h r hr)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations
