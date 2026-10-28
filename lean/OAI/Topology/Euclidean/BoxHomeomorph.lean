import OAI.Topology.Euclidean.BoxBasis
import OAI.Topology.Euclidean.OpenCoordinateTransport
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Order.MonotoneContinuity

/-! # Box Homeomorph -/

namespace OAI.Topology.Euclidean

noncomputable section

/-!
# Actual Euclidean homeomorphisms for rational open boxes

Each coordinate interval is homeomorphic to the real line. Taking products and
identifying a product of interval subtypes with the actual open-box subtype gives
the box homeomorphism. The final construction transports it through the explicit
real coordinates on a complex vector space. These are topological statements.
-/

open Set _root_.TopologicalSpace

/-- Every nonempty bounded open real interval is homeomorphic to the real line. -/
def BoxHomeomorph.Globalization.realOpenIntervalHomeomorph (a b : ℝ) (hab : a < b) : Ioo a b ≃ₜ ℝ := by
  have hs : 0 < (b - a) / 2 := by linarith
  let e : ℝ ≃ₜ ℝ := affineHomeomorph ((b - a) / 2) ((a + b) / 2) hs.ne'
  have himage : e '' Ioo (-1 : ℝ) 1 = Ioo a b := by
    dsimp [e]
    rw [affineHomeomorph_image_Ioo _ _ _ _ hs]
    congr 1 <;> ring
  exact ((e.image (Ioo (-1 : ℝ) 1)).trans (Homeomorph.setCongr himage)).symm.trans
    (orderIsoIooNegOneOne ℝ).toHomeomorph.symm

section

variable {ι : Type*}

/-- The open-box subtype is the product of its coordinate interval subtypes. -/
def BoxBasis.Globalization.RationalBox.productHomeomorph (B : BoxBasis.Globalization.RationalBox ι) :
    B.carrier ≃ₜ (∀ i, Ioo (B.lower i : ℝ) (B.upper i : ℝ)) where
  toFun x i := ⟨x.val i, (B.mem_carrier x.val).mp x.property i⟩
  invFun y := ⟨fun i => (y i).val, (B.mem_carrier _).mpr fun i => (y i).property⟩
  left_inv x := Subtype.ext rfl
  right_inv y := by
    funext i
    rfl
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)).subtype_mk _

@[simp]
theorem BoxBasis.Globalization.RationalBox.productHomeomorph_apply (B : BoxBasis.Globalization.RationalBox ι) (x : B.carrier) (i : ι) :
    (B.productHomeomorph x i : ℝ) = x.val i := rfl

@[simp]
theorem BoxBasis.Globalization.RationalBox.productHomeomorph_symm_apply (B : BoxBasis.Globalization.RationalBox ι)
    (y : ∀ i, Ioo (B.lower i : ℝ) (B.upper i : ℝ)) (i : ι) :
    (B.productHomeomorph.symm y).val i = (y i).val := rfl

/-- A rational open box is homeomorphic to the full real coordinate space.
The construction also works for an arbitrary, possibly infinite, index type. -/
def BoxBasis.Globalization.RationalBox.homeomorphEuclidean (B : BoxBasis.Globalization.RationalBox ι) : B.carrier ≃ₜ (ι → ℝ) :=
  B.productHomeomorph.trans (Homeomorph.piCongrRight fun i =>
    BoxHomeomorph.Globalization.realOpenIntervalHomeomorph (B.lower i : ℝ) (B.upper i : ℝ)
      (Rat.cast_lt.mpr (B.lower_lt_upper i)))

/-- Pulling a box back through a genuine ambient homeomorphism preserves its
Euclidean homeomorphism type. -/
def BoxBasis.Globalization.RationalBox.preimageHomeomorph {X : Type*} [TopologicalSpace X] (B : BoxBasis.Globalization.RationalBox ι)
    (e : X ≃ₜ (ι → ℝ)) : (e ⁻¹' B.carrier) ≃ₜ (ι → ℝ) :=
  (e.subtype fun _ => Iff.rfl).trans B.homeomorphEuclidean

/-- The actual open carrier of a finite-dimensional rational box. -/
def BoxBasis.Globalization.RationalBox.openCarrier [Finite ι] (B : BoxBasis.Globalization.RationalBox ι) : Opens (ι → ℝ) :=
  ⟨B.carrier, B.isOpen_carrier⟩

@[simp]
theorem BoxBasis.Globalization.RationalBox.coe_openCarrier [Finite ι] (B : BoxBasis.Globalization.RationalBox ι) :
    (B.openCarrier : Set (ι → ℝ)) = B.carrier := rfl

end

/-- The open subset of complex coordinate space corresponding to a real box. -/
def BoxHomeomorph.Globalization.complexBoxOpen (d : ℕ) (B : BoxBasis.Globalization.RationalBox (Fin (2 * d))) : Opens (Fin d → ℂ) :=
  OpenCoordinateTransport.Globalization.realOpenInComplexCoordinates d B.openCarrier

@[simp]
theorem BoxHomeomorph.Globalization.mem_complexBoxOpen (d : ℕ) (B : BoxBasis.Globalization.RationalBox (Fin (2 * d))) (z : Fin d → ℂ) :
    z ∈ BoxHomeomorph.Globalization.complexBoxOpen d B ↔ ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d z ∈ B.carrier :=
  Iff.rfl

/-- A real box of dimension `2 * d` has the underlying topological type of
complex coordinate space of dimension `d`. -/
def BoxHomeomorph.Globalization.realBoxComplexHomeomorph (d : ℕ) (B : BoxBasis.Globalization.RationalBox (Fin (2 * d))) :
    B.carrier ≃ₜ (Fin d → ℂ) :=
  B.homeomorphEuclidean.trans (ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).symm.toHomeomorph

/-- The actual complex-coordinate preimage of a real box is homeomorphic to the
full complex coordinate space. No holomorphic or orientation assertion is made. -/
def BoxHomeomorph.Globalization.complexBoxHomeomorph (d : ℕ) (B : BoxBasis.Globalization.RationalBox (Fin (2 * d))) :
    BoxHomeomorph.Globalization.complexBoxOpen d B ≃ₜ (Fin d → ℂ) :=
  (B.preimageHomeomorph (ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).toHomeomorph).trans
    (ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).symm.toHomeomorph

end

end OAI.Topology.Euclidean
