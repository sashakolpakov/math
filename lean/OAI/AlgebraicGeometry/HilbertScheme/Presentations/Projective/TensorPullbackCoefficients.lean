import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AffineSourceCoefficients
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientSourceTransport
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Tensor Pullback Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TensorPullbackCoefficients

noncomputable section

/-! Projective tensor coordinates give coefficient ideals on the actual
scheme-theoretic affine pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u
variable (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
variable [Module.Projective A (A ⊗[R] B)]

theorem projective_tensor_pullback_coefficients
    (K : (pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))).IdealSheafData) :
    ∃ I : Ideal A, Affine.IdealCoefficientTests.IsAffineIdealCoefficient A
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))) K I := by
  let hp := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R A B)).flip
  let e := hp.isoPullback
  obtain ⟨I, hI⟩ := AffineSourceCoefficients.projective_affine_source_coefficients A (CommRingCat.of (A ⊗[R] B))
    (K.comap e.hom)
  refine ⟨I, CoefficientSourceTransport.affineIdealCoefficient_transport_source A e _ K I ?_⟩
  rw [hp.isoPullback_hom_snd]
  exact hI

theorem projective_tensor_pullback_coefficients_of_eq
    (f : Spec B ⟶ Spec R)
    (hf : Spec.map (CommRingCat.ofHom (algebraMap R B)) = f)
    (K : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).IdealSheafData) :
    ∃ I : Ideal A, Affine.IdealCoefficientTests.IsAffineIdealCoefficient A
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))) K I := by
  subst f
  exact projective_tensor_pullback_coefficients R A B K

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TensorPullbackCoefficients
