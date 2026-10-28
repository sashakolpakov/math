import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Left Exact Homology -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomology

noncomputable section

/-!
# Homology comparison for a left exact functor

A functor preserving finite limits carries cycles to cycles. Passing the
mapped homology projection through the cokernel defining homology gives the
canonical map from the homology after applying the functor to the image of
homology. No preservation of cokernels is needed for this map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D]
  (S : ShortComplex C) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- The cycle object is preserved by a left exact functor. -/
def leftExactCyclesIso : (S.map F).cycles ≅ F.obj S.cycles :=
  ((S.map F).isoCyclesOfIsLimit
    (KernelFork.mapIsLimit _ S.cyclesIsKernel F)).symm

@[reassoc (attr := simp)]
theorem leftExactCyclesIso_hom_iCycles :
    (leftExactCyclesIso S F).hom ≫ F.map S.iCycles = (S.map F).iCycles :=
  (S.map F).isoCyclesOfIsLimit_inv_ι
    (KernelFork.mapIsLimit _ S.cyclesIsKernel F)

@[reassoc (attr := simp)]
theorem toCycles_leftExactCyclesIso_hom :
    (S.map F).toCycles ≫ (leftExactCyclesIso S F).hom = F.map S.toCycles := by
  apply (cancel_mono (F.map S.iCycles)).mp
  simp only [Category.assoc, leftExactCyclesIso_hom_iCycles,
    ShortComplex.toCycles_i, ← F.map_comp]
  rfl

/-- Canonical comparison on homology for a left exact functor. -/
def leftExactHomologyComparison : (S.map F).homology ⟶ F.obj S.homology :=
  (S.map F).descHomology ((leftExactCyclesIso S F).hom ≫ F.map S.homologyπ) (by
    rw [← Category.assoc, toCycles_leftExactCyclesIso_hom, ← F.map_comp,
      ShortComplex.toCycles_comp_homologyπ, F.map_zero])

@[reassoc (attr := simp)]
theorem homologyπ_leftExactHomologyComparison :
    (S.map F).homologyπ ≫ leftExactHomologyComparison S F =
      (leftExactCyclesIso S F).hom ≫ F.map S.homologyπ :=
  (S.map F).π_descHomology _ _

variable {S} {T : ShortComplex C}

@[reassoc]
theorem leftExactCyclesIso_naturality (f : S ⟶ T) :
    ShortComplex.cyclesMap (F.mapShortComplex.map f) ≫ (leftExactCyclesIso T F).hom =
      (leftExactCyclesIso S F).hom ≫ F.map (ShortComplex.cyclesMap f) := by
  dsimp only [Functor.mapShortComplex]
  apply (cancel_mono (F.map T.iCycles)).mp
  simp only [Category.assoc, leftExactCyclesIso_hom_iCycles,
    ShortComplex.cyclesMap_i, ← F.map_comp]
  rw [F.map_comp, ← Category.assoc,
    leftExactCyclesIso_hom_iCycles]

@[reassoc]
theorem leftExactHomologyComparison_naturality (f : S ⟶ T) :
    ShortComplex.homologyMap (F.mapShortComplex.map f) ≫ leftExactHomologyComparison T F =
      leftExactHomologyComparison S F ≫ F.map (ShortComplex.homologyMap f) := by
  have hcycles := leftExactCyclesIso_naturality F f
  dsimp only [Functor.mapShortComplex] at hcycles ⊢
  apply (cancel_epi (S.map F).homologyπ).mp
  rw [← Category.assoc, ShortComplex.homologyπ_naturality, Category.assoc,
    homologyπ_leftExactHomologyComparison, ← Category.assoc,
    hcycles, Category.assoc, ← F.map_comp,
    ← ShortComplex.homologyπ_naturality, F.map_comp,
    ← Category.assoc, ← homologyπ_leftExactHomologyComparison, Category.assoc]

end

end OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomology
