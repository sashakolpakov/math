import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ModelGlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionFrameCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.KernelExactCriterion

/-! # Model Specified Section Cycles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ModelSpecifiedSectionCycles

noncomputable section

/-! Actual sections have specified cycle representatives in a finite
Cech model. Their images under the model comparison are the actual Cech
cycles of those sections, and completeness is equivalent to bijectivity
of the specified kernel comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {R : Type u} [CommRing R]
variable (c : R →+* Γ(X, ⊤)) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} R) ℕ}
variable (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U) [QuasiIsoAt φ 0]

def orderedCechSectionKernelEquiv :
    (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M ≃ₗ[R]
      ((Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U).d 0 1).hom.ker :=
  OrderedCech.ZeroGluing.OrderedCechZeroCoordinates.sectionsEquiv c M U hU

def modelSectionKernelEquiv :
    (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M ≃ₗ[R] (D.d 0 1).hom.ker :=
  (ModelGlobalSections.CechModelSections.equiv c M U hU φ).symm

def modelSectionCycleMap {κ : Type v} (s : κ → (Line.Bundles.structureModule X ⟶ M)) :
    (κ →₀ R) →ₗ[R] D.X 0 :=
  (D.d 0 1).hom.ker.subtype.comp
    ((modelSectionKernelEquiv c M U hU φ).toLinearMap.comp
      (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s))

theorem modelSectionCycleMap_cycle {κ : Type v} (s : κ → (Line.Bundles.structureModule X ⟶ M)) :
    (D.d 0 1).hom.comp (modelSectionCycleMap c M U hU φ s) = 0 := by
  apply LinearMap.ext
  intro x
  exact (modelSectionKernelEquiv c M U hU φ
    (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s x)).property

theorem modelSectionCycleMap_comparison {κ : Type v}
    (s : κ → (Line.Bundles.structureModule X ⟶ M)) (x : κ →₀ R) :
    φ.f 0 (modelSectionCycleMap c M U hU φ s x) =
      (orderedCechSectionKernelEquiv c M U hU (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s x)).val := by
  let e := ModelGlobalSections.CechModelSections.equiv c M U hU φ
  let z := Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s x
  have h := ModelGlobalSections.CechModelSections.coordinate c M U hU φ (e.symm z)
  erw [LinearEquiv.apply_symm_apply] at h
  exact h

theorem modelSectionCycleMap_complete_iff {κ : Type v}
    (s : κ → (Line.Bundles.structureModule X ⟶ M)) :
    Function.Bijective (KernelDimensionCriterion.linearKernelComparison (modelSectionCycleMap c M U hU φ s)
      (D.d 0 1).hom (modelSectionCycleMap_cycle c M U hU φ s)) ↔
        Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s) := by
  let e := modelSectionKernelEquiv c M U hU φ
  let a := Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s
  change Function.Bijective (fun x => e (a x)) ↔ Function.Bijective a
  constructor
  · intro h
    refine ⟨fun x y hxy => h.injective (congrArg e hxy), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := h.surjective (e y)
    exact ⟨x, e.injective hx⟩
  · intro h
    exact e.bijective.comp h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ModelSpecifiedSectionCycles
