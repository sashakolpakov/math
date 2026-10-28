import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleCodimension
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleClassMap
import OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge

/-! # Dimension Cycle Supports -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports

noncomputable section

/-! # The exact same reduced cycle components in both geometric frameworks -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

/-- The original point-indexed cycle, with the unchanged actual reduced closed support. -/
def originalDimensionSupport (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p) :
    CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (V) p :=
  ⟨irreducibleSetEquivPoints.symm x.val, CycleCodimension.originalPoint_dimensionCodimension (V) x.val p x.property⟩

/-- The original codimension of the genuine generic point of a dimension-graded support. -/
def originalDimensionSupportGenericPoint (p : ℕ) (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (V) p) :
    CycleClassMap.OriginalCycleComponent X p := by
  let x := irreducibleSetEquivPoints D.val
  have hbound := AlgebraicGeometry.Smooth.DimensionFormula.SmoothOfRelativeDimension.coheight_le_complex
    (f := X.hom) (d := Topology.Dimension.Basic.TopologicalSpace.dim X.left) x
  have hfinite : Order.coheight x ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top (Topology.Dimension.Basic.TopologicalSpace.dim X.left)) hbound
  have hq : Order.coheight x = (Order.coheight x).toNat :=
    (ENat.natCast_toNat hfinite).symm
  have hd := CycleCodimension.originalPoint_dimensionCodimension (V) x (Order.coheight x).toNat hq
  dsimp only [x] at hd
  rw [irreducibleSetEquivPoints.symm_apply_apply] at hd
  have hp : (Order.coheight x).toNat = p := hd.symm.trans D.property
  exact ⟨x, hq.trans (congrArg (fun n : ℕ => (n : ℕ∞)) hp)⟩

/-- Both frameworks index exactly the same actual cycle supports in every codimension. -/
def originalDimensionSupportEquiv (p : ℕ) :
    CycleClassMap.OriginalCycleComponent X p ≃ CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (V) p where
  toFun := originalDimensionSupport X p
  invFun := originalDimensionSupportGenericPoint X p
  left_inv x := by
    apply Subtype.ext
    exact irreducibleSetEquivPoints.apply_symm_apply x.val
  right_inv D := by
    apply Subtype.ext
    exact irreducibleSetEquivPoints.symm_apply_apply D.val

/-- The cycle's reduced closed scheme is the literal original reduced closure. -/
theorem originalDimensionSupport_scheme (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p) :
    (originalDimensionSupport X p x).scheme = Cycle.Support.cycleComponent X.left x.val := rfl

/-- Its closed immersion is the same actual original subgroup-free cycle inclusion. -/
theorem originalDimensionSupport_inclusion (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p) :
    (originalDimensionSupport X p x).inclusion = Cycle.Support.cycleComponentι X.left x.val := rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports
