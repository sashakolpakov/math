import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalBlock
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalPlaneNeighborhood
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Normal Derivative -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalDerivative.Cycles

noncomputable section

/-!
# Derivatives of genuine normal coordinate changes

Restricting a differentiable map to the horizontal coordinate plane and
then projecting to its normal coordinate gives a locally zero map when
the original map preserves that plane. Uniqueness of the derivative makes
the lower-left derivative block zero. Applying the same argument to the
actual inverse proves the two preservation hypotheses needed by the
previously constructed complex normal-block equivalence.
-/

open Filter
open scoped _root_.Topology _root_.Manifold

section GeneralDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G H : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The lower-left derivative block vanishes when the normal component
of the restriction to the horizontal plane is locally zero. -/
theorem normalDerivative_lowerLeft_eq_zero
    {Φ : E × F → G × H} {D : (E × F) →L[𝕜] (G × H)}
    (hd : HasFDerivAt Φ D (0, 0))
    (hz : ∀ᶠ x : E in 𝓝 0, (Φ (x, 0)).2 = 0) :
    (ContinuousLinearMap.snd 𝕜 G H).comp
      (D.comp (ContinuousLinearMap.inl 𝕜 E F)) = 0 := by
  have hin : HasFDerivAt (fun x : E => (x, (0 : F)))
      (ContinuousLinearMap.inl 𝕜 E F) (0 : E) :=
    (ContinuousLinearMap.inl 𝕜 E F).hasFDerivAt
  have hrestrict : HasFDerivAt (fun x : E => (Φ (x, 0)).2)
      ((ContinuousLinearMap.snd 𝕜 G H).comp
        (D.comp (ContinuousLinearMap.inl 𝕜 E F))) 0 := by
    exact (hd.comp (0 : E) hin).snd
  exact hrestrict.unique
    ((hasFDerivAt_const (𝕜 := 𝕜) (0 : H) (0 : E)).congr_of_eventuallyEq hz)

/-- Consequently the actual derivative maps every horizontal tangent
vector to a horizontal vector. -/
theorem normalDerivative_preserves_horizontal
    {Φ : E × F → G × H} {D : (E × F) →L[𝕜] (G × H)}
    (hd : HasFDerivAt Φ D (0, 0))
    (hz : ∀ᶠ x : E in 𝓝 0, (Φ (x, 0)).2 = 0) (x : E) :
    (D (x, 0)).2 = 0 :=
  congrArg (fun L : E →L[𝕜] H => L x) (normalDerivative_lowerLeft_eq_zero hd hz)

/-- Actual source-plane preservation implies preservation by the
derivative; the neighborhood condition is derived from source openness. -/
theorem normalCoordinateDerivative_preserves_horizontal
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (D : (E × F) →L[𝕜] (E × F)) (h0 : (0, 0) ∈ e.source)
    (hd : HasFDerivAt e D (0, 0))
    (hpres : ∀ z ∈ e.source, z.2 = 0 → (e z).2 = 0) :
    ∀ x : E, (D (x, 0)).2 = 0 :=
  normalDerivative_preserves_horizontal hd
    (NormalPlaneNeighborhood.Cycles.normalPlane_eventually_map_snd_eq_zero e h0 hpres)

/-- The actual inverse has the inverse derivative at the origin. -/
theorem normalCoordinateInverse_hasFDerivAt
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[𝕜] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0)) :
    HasFDerivAt e.symm L.symm.toContinuousLinearMap (0, 0) := by
  apply e.hasFDerivAt_symm (NormalPlaneNeighborhood.Cycles.normalPlane_zero_mem_target e h0 he0)
  simpa only [NormalPlaneNeighborhood.Cycles.normalPlane_symm_apply_zero e h0 he0] using hd

/-- Actual preservation of the horizontal plane by the inverse gives
the corresponding preservation by the inverse derivative. -/
theorem normalCoordinateInverseDerivative_preserves_horizontal
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[𝕜] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0))
    (hpres : ∀ z ∈ e.target, z.2 = 0 → (e.symm z).2 = 0) :
    ∀ x : E, (L.symm (x, 0)).2 = 0 :=
  normalDerivative_preserves_horizontal
    (normalCoordinateInverse_hasFDerivAt e L h0 he0 hd)
    (NormalPlaneNeighborhood.Cycles.normalPlane_eventually_symm_snd_eq_zero e h0 he0 hpres)

/-- Exact preservation of the zero normal locus supplies both derivative
preservation laws, with no independent linear hypothesis. -/
theorem normalCoordinateDerivative_horizontal_pair
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[𝕜] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) :
    (∀ x : E, (L (x, 0)).2 = 0) ∧ (∀ x : E, (L.symm (x, 0)).2 = 0) := by
  constructor
  · exact normalCoordinateDerivative_preserves_horizontal e L.toContinuousLinearMap h0 hd
      (fun z hz => (hpres z hz).mpr)
  · exact normalDerivative_preserves_horizontal
      (normalCoordinateInverse_hasFDerivAt e L h0 he0 hd)
      (NormalPlaneNeighborhood.Cycles.normalPlane_eventually_symm_snd_eq_zero_of_iff e h0 he0 hpres)

end GeneralDerivative

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The genuine normal derivative is invertible, using the preservation
laws proved from the nonlinear map and its actual inverse. -/
def normalCoordinateDerivativeBlock
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[ℂ] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) : F ≃L[ℂ] F :=
  Geometric.ComplexNormalBlock.Cycles.normalBlock L (normalCoordinateDerivative_horizontal_pair e L h0 he0 hd hpres).1
    (normalCoordinateDerivative_horizontal_pair e L h0 he0 hd hpres).2

@[simp]
theorem normalCoordinateDerivativeBlock_apply
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[ℂ] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) (y : F) :
    normalCoordinateDerivativeBlock e L h0 he0 hd hpres y = (L (0, y)).2 := rfl

@[simp]
theorem normalCoordinateDerivativeBlock_symm_apply
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[ℂ] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) (y : F) :
    (normalCoordinateDerivativeBlock e L h0 he0 hd hpres).symm y =
      (L.symm (0, y)).2 := rfl

/-- The ambient derivative commutes with projection to the actual normal
block constructed above. -/
theorem normalCoordinateDerivativeBlock_projection
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (L : (E × F) ≃L[ℂ] (E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0)) (hd : HasFDerivAt e L.toContinuousLinearMap (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) (z : E × F) :
    (L z).2 = normalCoordinateDerivativeBlock e L h0 he0 hd hpres z.2 :=
  Geometric.ComplexNormalBlock.Cycles.normalBlock_projection L (normalCoordinateDerivative_horizontal_pair e L h0 he0 hd hpres).1
    (normalCoordinateDerivative_horizontal_pair e L h0 he0 hd hpres).2 z

/-- The ambient derivative of a genuine differentiable local
homeomorphism, with invertibility derived from its differentiable inverse. -/
def normalDiffeomorphDerivative
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (he : e.MDifferentiable 𝓘(ℂ, E × F) 𝓘(ℂ, E × F)) (h0 : (0, 0) ∈ e.source) :
    (E × F) ≃L[ℂ] (E × F) :=
  he.mfderiv h0

theorem normalDiffeomorphDerivative_coe
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (he : e.MDifferentiable 𝓘(ℂ, E × F) 𝓘(ℂ, E × F)) (h0 : (0, 0) ∈ e.source) :
    (normalDiffeomorphDerivative e he h0).toContinuousLinearMap = fderiv ℂ e (0, 0) :=
  mfderiv_eq_fderiv

theorem normalDiffeomorphDerivative_hasFDerivAt
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (he : e.MDifferentiable 𝓘(ℂ, E × F) 𝓘(ℂ, E × F)) (h0 : (0, 0) ∈ e.source) :
    HasFDerivAt e (normalDiffeomorphDerivative e he h0).toContinuousLinearMap (0, 0) := by
  rw [normalDiffeomorphDerivative_coe]
  exact (he.mdifferentiableAt h0).differentiableAt.hasFDerivAt

/-- A genuine complex local diffeomorphism preserving the normal zero
locus induces an invertible normal derivative, with no chosen derivative
or linear-preservation assumptions. -/
def normalDiffeomorphBlock
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (he : e.MDifferentiable 𝓘(ℂ, E × F) 𝓘(ℂ, E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) : F ≃L[ℂ] F :=
  normalCoordinateDerivativeBlock e (normalDiffeomorphDerivative e he h0) h0 he0
    (normalDiffeomorphDerivative_hasFDerivAt e he h0) hpres

theorem normalDiffeomorphBlock_apply
    (e : OpenPartialHomeomorph (E × F) (E × F))
    (he : e.MDifferentiable 𝓘(ℂ, E × F) 𝓘(ℂ, E × F)) (h0 : (0, 0) ∈ e.source)
    (he0 : e (0, 0) = (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) (y : F) :
    normalDiffeomorphBlock e he h0 he0 hpres y = (fderiv ℂ e (0, 0) (0, y)).2 := by
  change ((normalDiffeomorphDerivative e he h0).toContinuousLinearMap (0, y)).2 = _
  rw [normalDiffeomorphDerivative_coe]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalDerivative.Cycles
