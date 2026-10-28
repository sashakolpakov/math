import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.ProjectiveTransport
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Point Coordinate Coefficient Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Invertible point-coordinate transformations extend through
every coefficient homomorphism. Their action on extended vectors
is literal coefficient substitution, and frame orbit relations persist. -/
open TensorProduct
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] {ι : Type v} [Fintype ι] [DecidableEq ι]

def PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv (φ : R →+* A) (T : (ι → R) ≃ₗ[R] (ι → R)) :
    (ι → A) ≃ₗ[A] (ι → A) := by
  letI := φ.toAlgebra
  let E := TensorProduct.piScalarRight R A A ι
  exact E.symm.trans ((T.baseChange R A).trans E)

theorem PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv_apply_map (φ : R →+* A)
    (T : (ι → R) ≃ₗ[R] (ι → R)) (v : ι → R) :
    PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T (fun i => φ (v i)) = fun i => φ (T v i) := by
  let := φ.toAlgebra
  let E := TensorProduct.piScalarRight R A A ι
  have he : E.symm (fun i => φ (v i)) = (1 : A) ⊗ₜ[R] v :=
    TensorProduct.piScalarRight_symm_algebraMap R A ι v
  change E ((T.baseChange R A) (E.symm (fun i => φ (v i)))) = _
  rw [he, LinearEquiv.baseChange_tmul]
  funext i
  simp only [E, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Algebra.smul_def, mul_one]
  rfl

theorem Configuration.ProjectiveTransport.ConfigurationFrameRelated.map {n : ℕ} {κ : Type*}
    (φ : R →+* A) {v w : κ → Fin (n + 1) → R} (h : Configuration.ProjectiveTransport.ConfigurationFrameRelated v w) :
    Configuration.ProjectiveTransport.ConfigurationFrameRelated (fun z i => φ (v z i)) (fun z i => φ (w z i)) := by
  obtain ⟨T, s, hs⟩ := h
  refine ⟨PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T, fun z => Units.map φ (s z), fun z => ?_⟩
  funext i
  change φ (w z i) = φ (s z) * PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T (fun k => φ (v z k)) i
  rw [PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv_apply_map]
  exact (congrArg φ (congrFun (hs z) i)).trans (map_mul φ _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
