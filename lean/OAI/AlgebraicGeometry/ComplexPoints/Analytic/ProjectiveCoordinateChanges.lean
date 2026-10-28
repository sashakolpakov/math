import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCompactness
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveZeroLocus
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.ContinuousMap.Basic

/-! # Projective Coordinate Changes -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCoordinateChanges

/-!
# Continuous coordinate changes of projective space

The maps below are mathlib's projectivizations of actual linear maps, with the
ordinary quotient topology supplied by `ProjectiveCompactness`.
-/

section Semilinear

variable {K L V W : Type*} [DivisionRing K] [DivisionRing L]
  [AddCommGroup V] [Module K V] [TopologicalSpace V]
  [AddCommGroup W] [Module L W] [TopologicalSpace W]
  {σ : K →+* L}

/-- A continuous injective semilinear map induces a continuous map of lines. -/
theorem continuous_projectivization_map (f : V →ₛₗ[σ] W)
    (hf : Function.Injective f) (hc : Continuous f) :
    Continuous (Projectivization.map f hf) := by
  apply (ProjectiveCompactness.isQuotientMap_projectivization_mk' K V).continuous_iff.mpr
  exact (ProjectiveCompactness.continuous_projectivization_mk' L W).comp
    ((hc.comp continuous_subtype_val).subtype_mk
      (fun (v : {v : V // v ≠ 0}) => fun h => v.2 (hf (by simpa using h))))

/-- The bundled continuous map induced by an injective continuous semilinear map. -/
def projectivizationContinuousMap (f : V →ₛₗ[σ] W)
    (hf : Function.Injective f) (hc : Continuous f) :
    C(Projectivization K V, Projectivization L W) :=
  ⟨Projectivization.map f hf, continuous_projectivization_map f hf hc⟩

end Semilinear

section Linear

variable {K V W U : Type*} [DivisionRing K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V]
  [AddCommGroup W] [Module K W] [TopologicalSpace W]
  [AddCommGroup U] [Module K U] [TopologicalSpace U]

/-- An injective continuous linear map induces an injective map of projective spaces. -/
theorem projectivizationContinuousMap_injective (f : V →ₗ[K] W)
    (hf : Function.Injective f) (hc : Continuous f) :
    Function.Injective (projectivizationContinuousMap f hf hc) :=
  Projectivization.map_injective f hf

/-- A continuous linear equivalence induces a homeomorphism of projective spaces. -/
def projectivizationHomeomorph (e : V ≃L[K] W) :
    Projectivization K V ≃ₜ Projectivization K W where
  toFun := Projectivization.map e.toLinearEquiv.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearEquiv.toLinearMap e.symm.injective
  left_inv p := by
    induction p using Projectivization.ind with
    | h v hv => simp [Projectivization.map_mk]
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv => simp [Projectivization.map_mk]
  continuous_toFun := continuous_projectivization_map _ _ e.continuous
  continuous_invFun := continuous_projectivization_map _ _ e.symm.continuous

/-- The homeomorphism acts by the usual projectivization map. -/
theorem projectivizationHomeomorph_apply (e : V ≃L[K] W) (p : Projectivization K V) :
    projectivizationHomeomorph e p =
      Projectivization.map e.toLinearEquiv.toLinearMap e.injective p :=
  rfl

/-- Inverting a linear equivalence inverts its projective homeomorphism. -/
@[simp] theorem projectivizationHomeomorph_symm (e : V ≃L[K] W) :
    (projectivizationHomeomorph e).symm = projectivizationHomeomorph e.symm := by
  ext p
  rfl

/-- The identity change of coordinates induces the identity homeomorphism. -/
@[simp] theorem projectivizationHomeomorph_refl :
    projectivizationHomeomorph (ContinuousLinearEquiv.refl K V) =
      Homeomorph.refl (Projectivization K V) := by
  ext p
  induction p using Projectivization.ind with
  | h v hv => rfl

/-- Projectivization respects composition of continuous linear coordinate changes. -/
@[simp] theorem projectivizationHomeomorph_trans (e : V ≃L[K] W) (f : W ≃L[K] U) :
    (projectivizationHomeomorph e).trans (projectivizationHomeomorph f) =
      projectivizationHomeomorph (e.trans f) := by
  ext p
  induction p using Projectivization.ind with
  | h v hv => rfl

end Linear

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- A choice of finite basis identifies the projectivization with ordinary
finite-dimensional coordinate projective space by a homeomorphism. -/
noncomputable def projectivizationCoordinates :
    Projectivization ℂ V ≃ₜ Projectivization ℂ (Fin (Module.finrank ℂ V) → ℂ) :=
  projectivizationHomeomorph (Module.finBasis ℂ V).equivFunL

/-- The ordinary projectivization of any finite-dimensional complex normed space
is Hausdorff, by its coordinate homeomorphism. -/
theorem finiteDimensionalProjectivization_t2Space : T2Space (Projectivization ℂ V) :=
  (projectivizationCoordinates V).isEmbedding.t2Space

variable {V} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [FiniteDimensional ℂ W]

/-- An injective continuous linear map between finite-dimensional complex normed
spaces induces a closed embedding of their ordinary projective spaces. -/
theorem isClosedEmbedding_projectivization_map (f : V →L[ℂ] W)
    (hf : Function.Injective f) :
    Topology.IsClosedEmbedding (Projectivization.map f.toLinearMap hf) := by
  let : T2Space (Projectivization ℂ W) := finiteDimensionalProjectivization_t2Space W
  exact (continuous_projectivization_map f.toLinearMap hf f.continuous).isClosedEmbedding
    (Projectivization.map_injective f.toLinearMap hf)

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCoordinateChanges
