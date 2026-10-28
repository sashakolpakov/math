import OAI.Topology.Euclidean.ComplexModelRealCoordinates
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Opens

/-! # Open Coordinate Transport -/

namespace OAI.Topology.Euclidean.OpenCoordinateTransport.Globalization

noncomputable section

/-!
# Restricting smooth coordinate changes to actual open subsets

The open sets and their manifold structures below are mathlib's `Opens` and
canonical open-submanifold structures. Restriction keeps the ambient point map
and its inverse, and the transported open set is its exact image.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

section Restriction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {r : ℕ∞ω}

/-- The open-submanifold codomain criterion at any differentiability order.
This is the general charted-space subtype criterion applied to `ContMDiff`. -/
theorem contMDiff_subtypeVal_comp_iff_order (V : Opens N) (f : M → V) :
    ContMDiff I J r (Subtype.val ∘ f) ↔ ContMDiff I J r f := by
  unfold ContMDiff ContMDiffAt
  exact forall_congr' fun x => ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff f univ x

/-- Restrict a diffeomorphism to corresponding actual open subsets. -/
def restrictDiffeomorph (e : M ≃ₘ^r⟮I, J⟯ N) (U : Opens M) (V : Opens N)
    (hUV : ∀ x, x ∈ U ↔ e x ∈ V) : U ≃ₘ^r⟮I, J⟯ V where
  toEquiv := (e.toHomeomorph.subtype hUV).toEquiv
  contMDiff_toFun := by
    apply (contMDiff_subtypeVal_comp_iff_order V _).mp
    change ContMDiff I J r (fun x : U => e x.val)
    exact e.contMDiff.comp (contMDiff_subtype_val (I := I) (U := U))
  contMDiff_invFun := by
    apply (contMDiff_subtypeVal_comp_iff_order U _).mp
    change ContMDiff J I r (fun y : V => e.symm y.val)
    exact e.symm.contMDiff.comp (contMDiff_subtype_val (I := J) (U := V))

@[simp]
theorem restrictDiffeomorph_apply (e : M ≃ₘ^r⟮I, J⟯ N) (U : Opens M) (V : Opens N)
    (hUV : ∀ x, x ∈ U ↔ e x ∈ V) (x : U) :
    (restrictDiffeomorph e U V hUV x : N) = e x.val := rfl

@[simp]
theorem restrictDiffeomorph_symm_apply (e : M ≃ₘ^r⟮I, J⟯ N)
    (U : Opens M) (V : Opens N) (hUV : ∀ x, x ∈ U ↔ e x ∈ V) (y : V) :
    ((restrictDiffeomorph e U V hUV).symm y : M) = e.symm y.val := rfl

/-- The actual open image, using mathlib's order equivalence on open sets. -/
def diffeomorphImageOpen (e : M ≃ₘ^r⟮I, J⟯ N) (U : Opens M) : Opens N :=
  e.toHomeomorph.opensCongr U

theorem diffeomorphImageOpen_eq_preimage (e : M ≃ₘ^r⟮I, J⟯ N) (U : Opens M) :
    (diffeomorphImageOpen e U : Set N) = e.symm ⁻¹' (U : Set M) := rfl

theorem diffeomorphImageOpen_eq_image (e : M ≃ₘ^r⟮I, J⟯ N) (U : Opens M) :
    (diffeomorphImageOpen e U : Set N) = e '' (U : Set M) :=
  (e.image_eq_preimage_symm U).symm

@[simp]
theorem mem_diffeomorphImageOpen (e : M ≃ₘ^r⟮I, J⟯ N) (U : Opens M) (y : N) :
    y ∈ diffeomorphImageOpen e U ↔ e.symm y ∈ U := Iff.rfl

theorem preimage_diffeomorphImageOpen (e : M ≃ₘ^r⟮I, J⟯ N) (U : Opens M) :
    e ⁻¹' (diffeomorphImageOpen e U : Set N) = (U : Set M) := by
  ext x
  change e.symm (e x) ∈ U ↔ x ∈ U
  rw [e.symm_apply_apply]

theorem diffeomorphImageOpen_mono (e : M ≃ₘ^r⟮I, J⟯ N) :
    Monotone (diffeomorphImageOpen e) := e.toHomeomorph.opensCongr.monotone

/-- The restriction to an open set and its exact image is a diffeomorphism. -/
def imageOpenDiffeomorph (e : M ≃ₘ^r⟮I, J⟯ N) (U : Opens M) :
    U ≃ₘ^r⟮I, J⟯ diffeomorphImageOpen e U :=
  restrictDiffeomorph e U (diffeomorphImageOpen e U) fun x => by
    simp only [mem_diffeomorphImageOpen, e.symm_apply_apply]

@[simp]
theorem imageOpenDiffeomorph_apply (e : M ≃ₘ^r⟮I, J⟯ N) (U : Opens M) (x : U) :
    (imageOpenDiffeomorph e U x : N) = e x.val := rfl

@[simp]
theorem imageOpenDiffeomorph_symm_apply (e : M ≃ₘ^r⟮I, J⟯ N) (U : Opens M)
    (y : diffeomorphImageOpen e U) :
    ((imageOpenDiffeomorph e U).symm y : M) = e.symm y.val := rfl

/-- Coordinate transport commutes with inclusion of smaller open subsets. -/
theorem imageOpenDiffeomorph_inclusion (e : M ≃ₘ^r⟮I, J⟯ N)
    {U V : Opens M} (hUV : U ≤ V) (x : U) :
    imageOpenDiffeomorph e V (Opens.inclusion hUV x) =
      Opens.inclusion (diffeomorphImageOpen_mono e hUV) (imageOpenDiffeomorph e U x) :=
  Subtype.ext rfl

end Restriction

/-- A complex-coordinate open subset written in the explicit real coordinates. -/
def complexOpenInRealCoordinates (d : ℕ) (U : Opens (Fin d → ℂ)) :
    Opens (Fin (2 * d) → ℝ) :=
  (ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).toHomeomorph.opensCongr U

/-- A real-coordinate open subset written in the explicit complex coordinates. -/
def realOpenInComplexCoordinates (d : ℕ) (V : Opens (Fin (2 * d) → ℝ)) :
    Opens (Fin d → ℂ) :=
  (ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).toHomeomorph.symm.opensCongr V

theorem complexOpenInRealCoordinates_eq_preimage (d : ℕ) (U : Opens (Fin d → ℂ)) :
    (complexOpenInRealCoordinates d U : Set (Fin (2 * d) → ℝ)) =
      (ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).symm ⁻¹' (U : Set (Fin d → ℂ)) := rfl

theorem complexOpenInRealCoordinates_eq_image (d : ℕ) (U : Opens (Fin d → ℂ)) :
    (complexOpenInRealCoordinates d U : Set (Fin (2 * d) → ℝ)) =
      ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d '' (U : Set (Fin d → ℂ)) :=
  ((ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).toEquiv.image_eq_preimage_symm U).symm

theorem realOpenInComplexCoordinates_eq_preimage (d : ℕ)
    (V : Opens (Fin (2 * d) → ℝ)) :
    (realOpenInComplexCoordinates d V : Set (Fin d → ℂ)) =
      ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d ⁻¹' (V : Set (Fin (2 * d) → ℝ)) := rfl

theorem realOpenInComplexCoordinates_eq_image (d : ℕ) (V : Opens (Fin (2 * d) → ℝ)) :
    (realOpenInComplexCoordinates d V : Set (Fin d → ℂ)) =
      (ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).symm ''
        (V : Set (Fin (2 * d) → ℝ)) :=
  ((ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).toEquiv.symm.image_eq_preimage_symm V).symm

@[simp]
theorem realOpenInComplexCoordinates_complexOpen (d : ℕ) (U : Opens (Fin d → ℂ)) :
    realOpenInComplexCoordinates d (complexOpenInRealCoordinates d U) = U :=
  (ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).toHomeomorph.opensCongr.symm_apply_apply U

@[simp]
theorem complexOpenInRealCoordinates_realOpen (d : ℕ) (V : Opens (Fin (2 * d) → ℝ)) :
    complexOpenInRealCoordinates d (realOpenInComplexCoordinates d V) = V :=
  (ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).toHomeomorph.opensCongr.apply_symm_apply V

/-- The actual real-coordinate map restricts to every complex-coordinate open set. -/
def complexOpenRealDiffeomorph (d : ℕ) (r : ℕ∞ω) (U : Opens (Fin d → ℂ)) :
    U ≃ₘ^r⟮𝓘(ℝ, Fin d → ℂ), 𝓘(ℝ, Fin (2 * d) → ℝ)⟯
      complexOpenInRealCoordinates d U :=
  imageOpenDiffeomorph (ComplexModelRealCoordinates.Globalization.complexModelRealDiffeomorph d r) U

@[simp]
theorem complexOpenRealDiffeomorph_apply (d : ℕ) (r : ℕ∞ω) (U : Opens (Fin d → ℂ))
    (x : U) :
    (complexOpenRealDiffeomorph d r U x : Fin (2 * d) → ℝ) =
      ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d x.val := rfl

@[simp]
theorem complexOpenRealDiffeomorph_symm_apply (d : ℕ) (r : ℕ∞ω)
    (U : Opens (Fin d → ℂ)) (y : complexOpenInRealCoordinates d U) :
    ((complexOpenRealDiffeomorph d r U).symm y : Fin d → ℂ) =
      (ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).symm y.val := rfl

/-- The inverse coordinate map restricts to every real-coordinate open set. -/
def realOpenComplexDiffeomorph (d : ℕ) (r : ℕ∞ω) (V : Opens (Fin (2 * d) → ℝ)) :
    V ≃ₘ^r⟮𝓘(ℝ, Fin (2 * d) → ℝ), 𝓘(ℝ, Fin d → ℂ)⟯
      realOpenInComplexCoordinates d V :=
  imageOpenDiffeomorph (ComplexModelRealCoordinates.Globalization.complexModelRealDiffeomorph d r).symm V

@[simp]
theorem realOpenComplexDiffeomorph_apply (d : ℕ) (r : ℕ∞ω)
    (V : Opens (Fin (2 * d) → ℝ)) (y : V) :
    (realOpenComplexDiffeomorph d r V y : Fin d → ℂ) =
      (ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d).symm y.val := rfl

@[simp]
theorem realOpenComplexDiffeomorph_symm_apply (d : ℕ) (r : ℕ∞ω)
    (V : Opens (Fin (2 * d) → ℝ)) (x : realOpenInComplexCoordinates d V) :
    ((realOpenComplexDiffeomorph d r V).symm x : Fin (2 * d) → ℝ) =
      ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv d x.val := rfl

end

end OAI.Topology.Euclidean.OpenCoordinateTransport.Globalization
