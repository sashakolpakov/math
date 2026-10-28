import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGlobalLattice
import OAI.RepresentationTheory.Theta.Definitions

/-! # Intrinsic Ambient Regularity -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicAmbientRegularity.Intrinsic

noncomputable section

/-! Full GaussianConvergence gives ambient real-analytic regularity of the actual native
completed tensors at every positive Siegel matrix. No parameter-family
regularity hypothesis is introduced. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise ContDiff BoundedContinuousFunction

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGlobalLattice.Intrinsic

variable {I : Type} [Fintype I] [DecidableEq I]

def auxiliary (L : Submodule ℤ (I → ℝ)) (φ : L →ᵇ ℂ)
    (p : Matrix I I ℂ × Matrix I I ℂ) (ξ : I → ℂ) : ℂ :=
  AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) • AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear p.2) ξ * Definitions.theta L φ p.1 ξ

omit [DecidableEq I] in
theorem quadratic_factor_analytic :
    ContDiff ℂ ⊤ (fun w : (Matrix I I ℂ × Matrix I I ℂ) × (I → ℂ) =>
      AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) • AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear w.1.2) w.2) := by
  simp only [AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor,_root_.smul_apply,smul_eq_mul,AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear_apply,dotProduct,Matrix.mulVec]
  fun_prop

omit [DecidableEq I] in
theorem auxiliary_analytic (hE : Analysis.GaussianConvergenceInput I)
    (L : Submodule ℤ (I → ℝ)) [DiscreteTopology L] (φ : L →ᵇ ℂ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (W : Matrix I I ℂ) (ξ : I → ℂ) :
    ContDiffAt ℂ ⊤ (Function.uncurry (auxiliary L φ)) ((Z.matrix,W),ξ) := by
  have hp : ∀ p ∈ ({(Z.matrix,ξ)} : Set (Analysis.ThetaParameters I)), p.1 ∈ Definitions.siegelDomain := by
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact ⟨Z.symmetric,Z.imaginary_posDef⟩
  have ht : ContDiffAt ℂ ⊤ (fun p : Analysis.ThetaParameters I => Definitions.theta L φ p.1 p.2) (Z.matrix,ξ) :=
    (hE L φ {(Z.matrix,ξ)} isCompact_singleton hp 0).2.1 (Z.matrix,ξ) (Set.mem_singleton _)
  exact quadratic_factor_analytic.contDiffAt.mul
    (ht.comp ((Z.matrix,W),ξ) (contDiffAt_fst.fst.prodMk contDiffAt_snd))

theorem lattice_tensor_ambient (hE : Analysis.GaussianConvergenceInput I)
    (L : Submodule ℤ (I → ℝ)) [DiscreteTopology L] (φ : L →ᵇ ℂ)
    (a : ℕ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) : ContDiffAt ℝ ⊤ (Definitions.completedTensor L φ a) Z.matrix := by
  let W := (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹
  have hj : ContDiffAt ℂ ⊤
      (fun p : Matrix I I ℂ × Matrix I I ℂ => iteratedFDeriv ℂ a (auxiliary L φ p) 0) (Z.matrix,W) :=
    (Definitions.partial_iteratedFDeriv_contDiffAt (auxiliary_analytic hE L φ Z W 0) a).comp (Z.matrix,W)
      (contDiffAt_id.prodMk contDiffAt_const)
  have hc : ContDiffAt ℝ ⊤ (fun M : Matrix I I ℂ => (M,(AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary M)⁻¹)) Z.matrix :=
    contDiffAt_id.prodMk (Definitions.inverse_imaginary_contDiffAt Z)
  exact ((hj.restrict_scalars ℝ).comp Z.matrix hc).const_smul ((Nat.factorial a : ℂ)⁻¹)

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem completedTensor_ambient_contDiffAt (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hL : Adelic.DataTheta.Descent.LatticeIdentification B) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) : ContDiffAt ℝ ⊤ (Adelic.DataTheta.completedTensor B f a) Z.matrix := by
  obtain ⟨L,hLd,φ,_,_,ht⟩ := IntrinsicGlobalLattice.Intrinsic.global_lattice_presentation B hL f
  let : DiscreteTopology L := hLd
  have he : Adelic.DataTheta.completedTensor B f a = Definitions.completedTensor L φ a := funext (ht a)
  rw [he]
  exact lattice_tensor_ambient hE L φ a Z

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicAmbientRegularity.Intrinsic
