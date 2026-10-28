import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartModules
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartTransition
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Module Naturality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ModuleNaturality.Construction

noncomputable section

/-! Naturality of the actual affine infinitesimal module comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The actual chart module comparisons commute with open restriction. -/
theorem affineInfinitesimalSectionsModuleEquiv_restrict (n : ℕ) {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    (x : (RelativeStructureSections.Construction.relativeStructureSections f).obj (op U) ⧸
      (I ^ (n + 1) • ⊤ : Submodule R ((RelativeStructureSections.Construction.relativeStructureSections f).obj (op U)))) :
    ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f n V hV
        (((RelativeStructureSections.Construction.relativeStructureSections f).map (homOfLE h).op).hom.reduceModIdeal (I ^ (n + 1)) x) =
      ((RelativeStructureSections.Construction.relativeStructureSections
        (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)).map
        (homOfLE ((pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n)).preimage_mono h)).op)
          (ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f n U hU x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      rw [LinearMap.reduceModIdeal_apply, ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv_mk,
        ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv_mk]
      exact ConcreteCategory.congr_hom
        ((RelativeStructureSections.Construction.relativeStructureSectionsPullback f (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n))).naturality
          (homOfLE h).op) s

/-- The quotient transition computes the literal infinitesimal restriction on chart sections. -/
theorem affineInfinitesimalSectionsModuleEquiv_transition (n : ℕ) (U : X.Opens)
    (hU : IsAffineOpen U)
    (x : (RelativeStructureSections.Construction.relativeStructureSections f).obj (op U) ⧸
      (I ^ (n + 1 + 1) • ⊤ : Submodule R ((RelativeStructureSections.Construction.relativeStructureSections f).obj (op U)))) :
    (show Γ(Neighborhoods.Construction.infinitesimalNeighborhood I f n,
      pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U) from
      ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f n U hU
        (AdicCompletion.transitionMap I ((RelativeStructureSections.Construction.relativeStructureSections f).obj (op U))
          (Nat.le_succ (n + 1)) x)) =
      ChartTransition.Construction.infinitesimalChartSectionTransition I f n U
        (ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f (n + 1) U hU x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      change ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f n U hU (Submodule.Quotient.mk s) =
        ChartTransition.Construction.infinitesimalChartSectionTransition I f n U
          (ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f (n + 1) U hU (Submodule.Quotient.mk s))
      rw [ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv_mk, ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv_mk]
      exact (ConcreteCategory.congr_hom
        (ChartTransition.Construction.infinitesimalChartSectionTransition_pullback I f n U) s).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ModuleNaturality.Construction
