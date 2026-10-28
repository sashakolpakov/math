import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Characters
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-! # Generic Component Section -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericComponentSection.Lifts

noncomputable section

/-!
Choose the generic etale labels by splitting the actual surjective
component projection in q-torsion. The projection's Z/q-linearity follows
from its group law. Unique extension then constructs the integral split
block, so no integral section or product isomorphism is input.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup
attribute [local instance] Evaluated.Characters.Lifts.genericTest_preconnected

variable (R L : Type) [CommRing R] [Field L] [Algebra R L]
variable (q : ℕ) [Fact q.Prime]
variable {V W : Type} [AddCommGroup V] [Module (ZMod q) V]
  [AddCommGroup W] [Module (ZMod q) W]
variable (A : Over (Spec (.of R))) [GrpObj A]
variable (c : (Evaluated.Sections.Lifts.genericTest R L ⟶ A) ≃* Multiplicative V)
variable (π : A ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative W)).X) [IsMonHom π]

def genericComponentLabels : Multiplicative V →* Multiplicative W :=
  (Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)).toMonoidHom.comp
    ((Picard.PoincareBundle.Kernel.Scheme.pointsMap π (Evaluated.Sections.Lifts.genericTest R L)).comp c.symm.toMonoidHom)

def genericComponentLinear : V →ₗ[ZMod q] W :=
  (AddMonoidHom.toMultiplicative.symm (genericComponentLabels R L A c π)).toZModLinearMap q

variable (hπ : Function.Surjective (fun a : Evaluated.Sections.Lifts.genericTest R L ⟶ A => a ≫ π))

include hπ in
theorem genericComponentLinear_surjective :
    Function.Surjective (genericComponentLinear R L q A c π) := by
  intro w
  obtain ⟨a, ha⟩ := hπ ((Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)).symm
    (Multiplicative.ofAdd w))
  change a ≫ π = (Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)).symm
    (Multiplicative.ofAdd w) at ha
  refine ⟨(c a).toAdd, ?_⟩
  change (Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)
    (c.symm (c a) ≫ π)).toAdd = w
  rw [c.symm_apply_apply, ha, MulEquiv.apply_symm_apply]
  rfl

def genericComponentRightInverse : W →ₗ[ZMod q] V :=
  ((genericComponentLinear R L q A c π).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (genericComponentLinear_surjective R L q A c π hπ))).choose

theorem genericComponentRightInverse_comp :
    (genericComponentLinear R L q A c π).comp (genericComponentRightInverse R L q A c π hπ) =
      LinearMap.id :=
  ((genericComponentLinear R L q A c π).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (genericComponentLinear_surjective R L q A c π hπ))).choose_spec

def genericComponentSectionLabels : Multiplicative W →* (Evaluated.Sections.Lifts.genericTest R L ⟶ A) :=
  c.symm.toMonoidHom.comp (genericComponentRightInverse R L q A c π hπ).toAddMonoidHom.toMultiplicative

theorem genericComponentSectionLabels_projection (w : Multiplicative W) :
    genericComponentSectionLabels R L q A c π hπ w ≫ π =
      Evaluated.Sections.Lifts.sectionRestriction R L (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative W)).X
        (ConstantSections.Lifts.constantLabelSection (Spec (.of R)) (Multiplicative W) w) := by
  apply (Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)).injective
  have h := LinearMap.congr_fun (genericComponentRightInverse_comp R L q A c π hπ) w.toAdd
  change (Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)
    (genericComponentSectionLabels R L q A c π hπ w ≫ π)).toAdd = w.toAdd at h
  have hw : Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)
      (Evaluated.Sections.Lifts.sectionRestriction R L (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative W)).X
        (ConstantSections.Lifts.constantLabelSection (Spec (.of R)) (Multiplicative W) w)) = w := by
    have hf := Evaluated.Characters.Lifts.constantPointCoordinates_factor (Multiplicative W) (Evaluated.Sections.Lifts.genericTest R L)
      (IsLocalRing.closedPoint L)
      ((Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)).symm w)
    change (Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)).symm w =
      CategoryTheory.CartesianMonoidalCategory.toUnit (Evaluated.Sections.Lifts.genericTest R L) ≫
        ConstantSections.Lifts.constantLabelSection (Spec (.of R)) (Multiplicative W)
          (Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)
            ((Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)).symm w)) at hf
    rw [MulEquiv.apply_symm_apply] at hf
    change Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)
      (CategoryTheory.CartesianMonoidalCategory.toUnit (Evaluated.Sections.Lifts.genericTest R L) ≫
        ConstantSections.Lifts.constantLabelSection (Spec (.of R)) (Multiplicative W) w) = w
    rw [← hf, MulEquiv.apply_symm_apply]
  rw [hw]
  exact Multiplicative.ext h

variable [IsDomain R] [ValuationRing R] [IsFractionRing R L] [IsProper A.hom]
variable [Finite W] [IsCommMonObj A]

/-- Construct the integral product splitting from the actual evaluated
generic q-torsion and its component projection. -/
def splitEvaluatedComponent :
    Picard.PoincareBundle.Kernel.Scheme.kernelObject π ⊗ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative W)).X ≅ A :=
  Evaluated.Splitting.Lifts.evaluatedComponentSplit R L A π (genericComponentSectionLabels R L q A c π hπ)
    (genericComponentSectionLabels_projection R L q A c π hπ)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericComponentSection.Lifts
