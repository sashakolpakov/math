import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FamilyEquationOperations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EqualizerIdealCriterion

/-! # Family Equation Universal Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-! A natural family equation on a represented parameter functor is
exactly the vanishing of the pulled-back ideal of one actual equalizer. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {M X Y T : Over S}

theorem FamilyEquationUniversalIdeal.Core.homTransformation_evaluation (φ : yoneda.obj M ⟶ HomFunctor.Hom.morphismFunctor X Y) (x : T ⟶ M) :
    φ.app (.op T) x = prod.map x (𝟙 X) ≫ φ.app (.op M) (𝟙 M) := by
  have h := ConcreteCategory.congr_hom (φ.naturality x.op) (𝟙 M)
  change φ.app (.op T) (x ≫ 𝟙 M) = prod.map x (𝟙 X) ≫ φ.app (.op M) (𝟙 M) at h
  simpa only [Category.comp_id] using h

def Endomorphisms.Core.FamilyMorphismEquation.universalIdeal (r : Endomorphisms.Core.FamilyMorphismEquation (yoneda.obj M)) :
    (M ⨯ r.source).left.IdealSheafData :=
  (equalizer.ι (r.lhs.app (.op M) (𝟙 M)) (r.rhs.app (.op M) (𝟙 M))).left.ker

theorem Endomorphisms.Core.FamilyMorphismEquation.universalIdeal_comap_eq_bot_iff
    (r : Endomorphisms.Core.FamilyMorphismEquation (yoneda.obj M)) (x : T ⟶ M) :
    r.universalIdeal.comap (prod.map x (𝟙 r.source)).left = ⊥ ↔
      r.lhs.app (.op T) x = r.rhs.app (.op T) x := by
  let := r.separated
  rw [FamilyEquationUniversalIdeal.Core.homTransformation_evaluation r.lhs x, FamilyEquationUniversalIdeal.Core.homTransformation_evaluation r.rhs x]
  exact EqualizerIdealCriterion.equalizer_ideal_comap_eq_bot_iff _ _ _

theorem FamilyEquationUniversalIdeal.Core.satisfiesEquations_iff_universalIdeals
    (R : List (Endomorphisms.Core.FamilyMorphismEquation (yoneda.obj M))) (x : T ⟶ M) :
    Endomorphisms.Core.SatisfiesEquations R x ↔ ∀ r ∈ R,
      r.universalIdeal.comap (prod.map x (𝟙 r.source)).left = ⊥ := by
  constructor
  · intro h r hr
    exact (r.universalIdeal_comap_eq_bot_iff x).mpr (h r hr)
  · intro h r hr
    exact (r.universalIdeal_comap_eq_bot_iff x).mp (h r hr)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations
