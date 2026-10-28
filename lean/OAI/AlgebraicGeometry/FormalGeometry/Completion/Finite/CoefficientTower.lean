import OAI.AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Limits

/-! # Coefficient Tower -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientTower.Construction

noncomputable section

/-!
# Completion: the actual coefficient sheaf is a limit of finite coefficient sheaves

The cone consists of the checked reduction morphisms. Its universal
property follows from reconstruction on sections, and degree-zero
transition maps are surjective.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})

theorem finiteEllAdicTransition_id (n : ℕ) : CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n n le_rfl X = 𝟙 _ := by
  apply (cancel_epi (CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X)).mp
  rw [CoefficientSheafLimit.Construction.finiteEllAdicReduction_transition, Category.comp_id]

theorem finiteEllAdicTransition_comp (m n p : ℕ) (hmn : m ≤ n) (hnp : n ≤ p) :
    CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n p hnp X ≫ CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ m n hmn X =
      CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ m p (hmn.trans hnp) X := by
  apply (cancel_epi (CoefficientSheaf.Construction.finiteEllAdicReduction ℓ p X)).mp
  rw [← Category.assoc, CoefficientSheafLimit.Construction.finiteEllAdicReduction_transition,
    CoefficientSheafLimit.Construction.finiteEllAdicReduction_transition, CoefficientSheafLimit.Construction.finiteEllAdicReduction_transition]

/-- The inverse diagram of actual finite coefficient sheaves. -/
def finiteCoefficientTower : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} where
  obj n := CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n.unop X
  map {n m} f := CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ m.unop n.unop (leOfHom f.unop) X
  map_id n := finiteEllAdicTransition_id ℓ X n.unop
  map_comp {n m p} _ _ := (finiteEllAdicTransition_comp ℓ X p.unop m.unop n.unop _ _).symm

/-- The cone of actual integral-to-finite reductions. -/
def integralCoefficientCone : Cone (finiteCoefficientTower ℓ X) where
  pt := ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X
  π := {
    app n := CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n.unop X
    naturality n m f := by
      simpa [finiteCoefficientTower] using!
        (CoefficientSheafLimit.Construction.finiteEllAdicReduction_transition ℓ X m.unop n.unop (leOfHom f.unop)).symm }

/-- Integral coefficients satisfy the inverse-limit universal property as sheaves. -/
def integralCoefficientConeIsLimit : IsLimit (integralCoefficientCone ℓ X) := by
  apply isLimitOfReflects (sheafToPresheaf _ Ab.{u + 1})
  apply evaluationJointlyReflectsLimits
  intro U
  apply isLimitOfReflects (forget Ab.{u + 1})
  apply Classical.choice
  apply (Types.isLimit_iff _).mpr
  intro s hs
  obtain ⟨a, ha, huniq⟩ := CoefficientSheafLimit.Construction.integralCoefficientSections_existsUnique ℓ X U
    (fun n => s (op n)) (fun m n h => hs (homOfLE h).op)
  exact ⟨a, fun n => ha n.unop, fun b hb => huniq b (fun n => hb (op n))⟩

/-- Degree-zero finite-coefficient transitions are surjective. -/
theorem finiteEllAdicTransition_H0_surjective (m n : ℕ) (h : m ≤ n) :
    Function.Surjective (Sheaf.H.map (CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ m n h X) 0) := by
  intro y
  obtain ⟨x, hx⟩ := CoefficientCohomology.Construction.integralEllAdicFiniteReduction_zero_surjective ℓ m X y
  refine ⟨CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n X 0 x, ?_⟩
  change (Sheaf.H.map (CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ m n h X) 0)
    (Sheaf.H.map (CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X) 0 x) = y
  rw [← Sheaf.H.map_comp_apply, CoefficientSheafLimit.Construction.finiteEllAdicReduction_transition]
  exact hx

/-- The transitions are surjective on maps from the actual integer constant sheaf. -/
theorem finiteEllAdicTransition_constantHom_surjective (m n : ℕ) (h : m ≤ n) :
    Function.Surjective (fun d : ProetalePullback.Construction.proEtIntegerConstant X ⟶ CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X =>
      d ≫ CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ m n h X) := by
  intro d
  obtain ⟨y, hy⟩ := finiteEllAdicTransition_H0_surjective ℓ X m n h (Ext.mk₀ d)
  obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  refine ⟨b, (Ext.mk₀_bijective _ _).injective ?_⟩
  simpa only [Sheaf.H.map_apply, Ext.mk₀_comp_mk₀] using hy

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientTower.Construction
