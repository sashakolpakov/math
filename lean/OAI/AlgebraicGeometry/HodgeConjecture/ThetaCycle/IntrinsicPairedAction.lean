import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PairedComplexification
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicGeometricAction

/-! # Intrinsic Paired Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicPairedAction.CM

noncomputable section

/-! The actual paired CM tensor action intertwines with the native
geometric action after normalization. The identity is derived from the
real tensor representation by complexification. -/

open scoped Classical _root_.NumberField Kronecker
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.TensorGeometricAction
open OAI.RepresentationTheory.Theta.Adelic.IntrinsicGeometricAction.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H)

def nativeUnnormalizedTensorMatrix (v : Fin A.places) :
    Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ :=
  ((g (A.enumerate v)).val.val.map (A.complex v)) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)

def nativePairedActionLinear : RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A →ₗ[ℂ] RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A :=
  LinearMap.pi (fun v =>
    ((Matrix.mulVecLin (nativeUnnormalizedTensorMatrix A g v)).prodMap
      (Matrix.mulVecLin ((nativeUnnormalizedTensorMatrix A g v).map star))).comp (LinearMap.proj v))

theorem native_paired_action_conjugate (x : Fin A.places → Fin 3 × Fin m → ℂ) :
    nativePairedActionLinear A g (fun v => (x v, fun j => star (x v j))) =
      fun v => ((nativeUnnormalizedTensorMatrix A g v).mulVec (x v),
        fun j => star ((nativeUnnormalizedTensorMatrix A g v).mulVec (x v) j)) := by
  funext v
  apply Prod.ext
  · rfl
  · exact (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.conjugate_mulVec (nativeUnnormalizedTensorMatrix A g v) (x v)).symm

theorem native_paired_components_action_linear :
    (IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents A).comp (nativePairedActionLinear A g) =
      (RepresentationTheory.Theta.Adelic.TensorGeometricAction.geometricActionLinear A g).comp (IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents A) := by
  apply PairedComplexification.CM.paired_complex_linear_ext
  intro x
  let s := fun (v : Fin A.places) (j : Fin 3 × Fin m) => (A.complex v).symm (x v j)
  have hs := IntrinsicTensorComplexCoordinates.CM.native_real_tensor_components_of_values A s x
    (fun v j => (A.complex v).apply_symm_apply (x v j))
  have ht := IntrinsicTensorComplexCoordinates.CM.native_real_tensor_components_of_values A (RepresentationTheory.Theta.Adelic.IntrinsicGeometricAction.Intrinsic.nativeTensorAction A g s)
    (fun v => (nativeUnnormalizedTensorMatrix A g v).mulVec (x v)) (by
      intro v j
      have he := congrFun (RepresentationTheory.Theta.Adelic.IntrinsicGeometricAction.Intrinsic.complex_native_tensor_action A g s v) j
      simpa only [s, RingEquiv.apply_symm_apply] using! he)
  have hl := congrArg (IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents A) (native_paired_action_conjugate A g x)
  have hg := (RepresentationTheory.Theta.Adelic.IntrinsicGeometricAction.Intrinsic.native_geometric_action A g s).symm
  have he := congrArg (RepresentationTheory.Theta.Adelic.BallGeometryData.geometricAction A g) hs
  exact hl.trans (ht.symm.trans (hg.trans (he.trans
    (RepresentationTheory.Theta.Adelic.TensorGeometricAction.geometricActionLinear_apply A g _).symm)))

theorem native_paired_components_action (w : RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A) :
    IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents A (nativePairedActionLinear A g w) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricAction A g (IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents A w) :=
  (LinearMap.congr_fun (native_paired_components_action_linear A g) w).trans
    (RepresentationTheory.Theta.Adelic.TensorGeometricAction.geometricActionLinear_apply A g _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicPairedAction.CM
