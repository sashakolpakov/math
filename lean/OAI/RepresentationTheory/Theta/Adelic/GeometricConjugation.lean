import OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates

/-! # Geometric Conjugation -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeometricConjugation

noncomputable section

/-! The real structure in standard/dual tensor coordinates is the
complexification of the actual real trace tensor space. -/

open scoped Classical _root_.NumberField ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates
open OAI.RepresentationTheory.Theta.Adelic.ComplexLinearExtension.PairedComplexification

theorem pairedComplexMap_conjugate {I J : Type*} [Fintype I]
    (e : (I → ℝ) ≃ₗ[ℝ] (J → ℂ)) (z : I → ℂ) :
    ComplexLinearExtension.PairedComplexification.pairedComplexMap e (fun i => conj (z i)) =
      (fun j => conj ((ComplexLinearExtension.PairedComplexification.pairedComplexMap e z).2 j),
       fun j => conj ((ComplexLinearExtension.PairedComplexification.pairedComplexMap e z).1 j)) := by
  have hneg (j : J) : e (fun i => -(z i).im) j = -(e (fun i => (z i).im) j) :=
    congrFun (e.map_neg (fun i => (z i).im)) j
  apply Prod.ext
  · funext j
    change (ComplexLinearExtension.PairedComplexification.pairedComplexMap e (fun i => conj (z i))).1 j = conj ((ComplexLinearExtension.PairedComplexification.pairedComplexMap e z).2 j)
    rw [ComplexLinearExtension.PairedComplexification.pairedComplexMap_first, ComplexLinearExtension.PairedComplexification.pairedComplexMap_second]
    simp only [Complex.conj_re, Complex.conj_im, hneg, map_add, map_mul,
      Complex.conj_I, Complex.conj_conj]
    ring
  · funext j
    change (ComplexLinearExtension.PairedComplexification.pairedComplexMap e (fun i => conj (z i))).2 j = conj ((ComplexLinearExtension.PairedComplexification.pairedComplexMap e z).1 j)
    rw [ComplexLinearExtension.PairedComplexification.pairedComplexMap_second, ComplexLinearExtension.PairedComplexification.pairedComplexMap_first]
    simp only [Complex.conj_re, Complex.conj_im, hneg, map_neg, map_add, map_mul, Complex.conj_I]
    ring

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def geometricConj (w : BallGeometryData.ComplexPhase A) : BallGeometryData.ComplexPhase A :=
  fun v => (fun ij => ComplexPhaseCoordinates.tensorDualSign A (v, ij) * conj ((w v).2 ij),
    fun ij => ComplexPhaseCoordinates.tensorDualSign A (v, ij) * conj ((w v).1 ij))

theorem tensorDualSign_conj (i : BallGeometryData.FrameIndex A) : conj (ComplexPhaseCoordinates.tensorDualSign A i) = ComplexPhaseCoordinates.tensorDualSign A i := by
  dsimp [ComplexPhaseCoordinates.tensorDualSign]
  split_ifs <;> norm_num

theorem pairedTensorEquiv_conjugate (w : (BallGeometryData.FrameIndex A → ℂ) × (BallGeometryData.FrameIndex A → ℂ)) :
    geometricConj A (ComplexPhaseCoordinates.pairedTensorEquiv A w) =
      ComplexPhaseCoordinates.pairedTensorEquiv A (fun i => conj (w.2 i), fun i => conj (w.1 i)) := by
  funext v
  apply Prod.ext
  · funext ij
    change ComplexPhaseCoordinates.tensorDualSign A (v, ij) * conj (ComplexPhaseCoordinates.tensorDualSign A (v, ij) * w.2 (v, ij)) = _
    rw [map_mul, tensorDualSign_conj, ← mul_assoc, ComplexPhaseCoordinates.tensorDualSign_mul_self, one_mul]
    rfl
  · rfl

theorem complexPhaseCoordinates_conjugate (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)
    (x : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℂ) :
    ComplexPhaseCoordinates.complexPhaseCoordinates A P (fun i => conj (x i)) =
      geometricConj A (ComplexPhaseCoordinates.complexPhaseCoordinates A P x) := by
  change ComplexPhaseCoordinates.pairedTensorEquiv A (ComplexLinearExtension.PairedComplexification.pairedComplexMap (ComplexPhaseCoordinates.flatRealTensorLinearEquiv A P)
    (fun i => conj (x i))) = geometricConj A (ComplexPhaseCoordinates.pairedTensorEquiv A
      (ComplexLinearExtension.PairedComplexification.pairedComplexMap (ComplexPhaseCoordinates.flatRealTensorLinearEquiv A P) x))
  rw [pairedComplexMap_conjugate, pairedTensorEquiv_conjugate]

end

end OAI.RepresentationTheory.Theta.Adelic.GeometricConjugation
