import OAI.AlgebraicGeometry.CycleClass.Geometric.ProjectiveComponentDimension
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.SumProd

/-! # Projective Component Cycles -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Rational cycles on the integral components of a projective variety

The codimension-preserving equivalence of actual irreducible supports induces
a linear equivalence between rational cycles on a smooth projective
presentation and a family of rational cycles on its integral components.
There are finitely many components by Noetherianity, so an arbitrary such
family still gives a finite cycle on the original variety.
-/

open _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- Rational finite cycles, with codimension measured in the actual integral
component containing each irreducible support. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.RationalDimensionCycle (p : ℕ) := P.DimensionCycleSupport p →₀ ℚ

/-- A rational cycle is exactly a family of rational cycles on the finitely
many integral components. This also permits components of different dimensions. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionCycleEquiv (p : ℕ) :
    P.RationalDimensionCycle p ≃ₗ[ℚ]
      ∀ C : irreducibleComponents P.carrier,
        CycleClass.Geometric.DimensionCycles.RationalDimensionCycle (P.componentVariety C) p := by
  classical
  let := Fintype.ofFinite (irreducibleComponents P.carrier)
  exact (Finsupp.domLCongr (P.componentDimensionSupportEquiv p)).trans
    (Finsupp.sigmaFinsuppLEquivPiFinsupp ℚ)

/-- The component coefficient is the original coefficient on the image
of precisely that support. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionCycleEquiv_apply (p : ℕ)
    (z : P.RationalDimensionCycle p) (C : irreducibleComponents P.carrier)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (P.componentVariety C) p) :
    P.componentDimensionCycleEquiv p z C Z =
      z ((P.componentDimensionSupportEquiv p).symm ⟨C, Z⟩) := rfl

/-- Reassembling the component cycles keeps every support coefficient. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionCycleEquiv_symm_apply (p : ℕ)
    (z : ∀ C : irreducibleComponents P.carrier,
      CycleClass.Geometric.DimensionCycles.RationalDimensionCycle (P.componentVariety C) p)
    (Z : P.DimensionCycleSupport p) :
    (P.componentDimensionCycleEquiv p).symm z Z =
      z (P.componentDimensionSupportEquiv p Z).1
        (P.componentDimensionSupportEquiv p Z).2 := rfl

/-- The forward map returns the given coefficient in the unique component
and support corresponding to the original support. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionCycleEquiv_apply_image (p : ℕ)
    (z : P.RationalDimensionCycle p) (Z : P.DimensionCycleSupport p) :
    P.componentDimensionCycleEquiv p z (P.componentDimensionSupportEquiv p Z).1
        (P.componentDimensionSupportEquiv p Z).2 = z Z := by
  rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionCycleEquiv_apply]
  exact congrArg z ((P.componentDimensionSupportEquiv p).symm_apply_apply Z)

/-- Reassembly at the image of a component support returns exactly its
component coefficient. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionCycleEquiv_symm_apply_image (p : ℕ)
    (z : ∀ C : irreducibleComponents P.carrier,
      CycleClass.Geometric.DimensionCycles.RationalDimensionCycle (P.componentVariety C) p)
    (C : irreducibleComponents P.carrier)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (P.componentVariety C) p) :
    (P.componentDimensionCycleEquiv p).symm z
        ((P.componentDimensionSupportEquiv p).symm ⟨C, Z⟩) = z C Z := by
  exact congrArg
    (fun W : Σ D : irreducibleComponents P.carrier,
      CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (P.componentVariety D) p => z W.1 W.2)
    ((P.componentDimensionSupportEquiv p).apply_symm_apply ⟨C, Z⟩)

/-- A single support keeps its multiplicity and is sent only to the
corresponding component support. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionCycleEquiv_single_apply (p : ℕ)
    (Z : P.DimensionCycleSupport p) (q : ℚ)
    (C : irreducibleComponents P.carrier)
    (W : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (P.componentVariety C) p) :
    P.componentDimensionCycleEquiv p (Finsupp.single Z q) C W =
      Finsupp.single (P.componentDimensionSupportEquiv p Z) q ⟨C, W⟩ := by
  classical
  simp only [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionCycleEquiv_apply, Finsupp.single_apply,
    Equiv.eq_symm_apply]

/-- A component's single cycle is unchanged on that component. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionCycleEquiv_single_same (p : ℕ)
    (C : irreducibleComponents P.carrier)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (P.componentVariety C) p) (q : ℚ) :
    P.componentDimensionCycleEquiv p
        (Finsupp.single ((P.componentDimensionSupportEquiv p).symm ⟨C, Z⟩) q) C =
      Finsupp.single Z q := by
  classical
  ext W
  simp only [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionCycleEquiv_single_apply, Equiv.apply_symm_apply,
    Finsupp.single_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and]

/-- A cycle supported on one component has zero coefficient on every
different component. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionCycleEquiv_single_ne (p : ℕ)
    (C D : irreducibleComponents P.carrier)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (P.componentVariety C) p) (q : ℚ)
    (hCD : C ≠ D) :
    P.componentDimensionCycleEquiv p
        (Finsupp.single ((P.componentDimensionSupportEquiv p).symm ⟨C, Z⟩) q) D = 0 := by
  classical
  ext W
  rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionCycleEquiv_single_apply, Equiv.apply_symm_apply,
    Finsupp.single_apply, Finsupp.zero_apply]
  exact ite_eq_right (fun h => hCD (congrArg Sigma.fst h))

end

end OAI.AlgebraicGeometry
