import OAI.NumberTheory.ArithmeticGroups.Lattices.RealSpecialLinearCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraTensorForms
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.TensorClosedImage

/-! # Real Closed Image -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.RealClosedImage.Construction

noncomputable section

/-! The full archimedean group has closed image in the real lattice
quotient. Scalar-multiplication and determinant tensors supply the
integral closed-orbit argument. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding MulAction

theorem minkowski_real_quotient_image_closed
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (b : Module.Basis (Fin m) ℝ (Fin n → mixedSpace k))
    (hb : Submodule.span ℤ (Set.range b) = IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) :
    let Γ := (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b)
      (IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module)).comap Matrix.SpecialLinearGroup.toGL
    IsClosed ((QuotientGroup.mk : Algebraic.SL m ℝ → Algebraic.SL m ℝ ⧸ Γ) ''
      ((RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n)
        (Archimedean.Quotient.Construction.archimedeanRealRepresentation_det k n) b).range : Set (Algebraic.SL m ℝ))) := by
  let E := Fin n → mixedSpace k
  let A := mixedSpace k
  let H := Algebraic.SL m ℝ
  let ρ := RealSpecialLinearCoordinates.Construction.specialFrameRepresentation b
  let τ : H →* (A ≃ₗ[ℝ] A) := 1
  let Λ := IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module
  let Ω := mixedEmbedding.integerLattice k
  let Γ := (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ).comap Matrix.SpecialLinearGroup.toGL
  let U := (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := E) b 1).range
  let D := (MultilinearBasisCoordinates.Construction.multilinearBasisEvaluation (A := A) b n).range
  let ρU := MultilinearAction.Construction.multilinearCovariantBasisRepresentation ρ ρ b 1
  let ρD := MultilinearAction.Construction.multilinearCovariantBasisRepresentation ρ τ b n
  let : MulAction H U := MulAction.compHom U ρU
  let : MulAction H D := MulAction.compHom D ρD
  have hρ : Continuous (fun a : H × E => ρ a.1 a.2) := RealSpecialLinearCoordinates.Construction.continuous_specialFrameRepresentation b
  have hτ : Continuous (fun a : H × A => τ a.1 a.2) := continuous_snd
  let : ContinuousSMul H U := ⟨MultilinearAction.Construction.continuous_multilinearCovariantBasisRepresentation ρ ρ b 1 hρ hρ⟩
  let : ContinuousSMul H D := ⟨MultilinearAction.Construction.continuous_multilinearCovariantBasisRepresentation ρ τ b n hρ hτ⟩
  let : DiscreteTopology Λ := IntegralLattice.Construction.vectorLatticeImage_discrete _ (IntegralLattice.FullLattice.standard k n).finite
  let L := MultilinearAction.Construction.integralMultilinearCoordinates b 1 Λ
  let M := MultilinearAction.Construction.integralMultilinearCoordinates b n Ω
  let x : Module.Free.ChooseBasisIndex ℤ (𝓞 k) → U := fun j =>
    MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b 1 (AlgebraTensorForms.Construction.scalarUnaryForm n (mixedEmbedding.latticeBasis k j))
  let y : D := MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b n (AlgebraTensorForms.Construction.algebraDeterminantForm (R := ℝ) n)
  have hbmem (i : Fin m) : b i ∈ Λ := by
    change b i ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module
    rw [← hb]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hx (j : Module.Free.ChooseBasisIndex ℤ (𝓞 k)) : x j ∈ L := by
    change MultilinearBasisCoordinates.Construction.multilinearBasisEvaluationEquiv b 1 (AlgebraTensorForms.Construction.scalarUnaryForm n (mixedEmbedding.latticeBasis k j)) ∈ L
    rw [mixedEmbedding.latticeBasis_apply, NumberField.integralBasis_apply]
    exact AlgebraTensorForms.Construction.scalarUnaryForm_integral_coordinates b hbmem (Module.Free.chooseBasis ℤ (𝓞 k) j)
  have hy : y ∈ M := AlgebraTensorForms.Construction.algebraDeterminantForm_integral_coordinates b hbmem
  have hΓ (g : H) (hg : g ∈ Γ) (v : E) (hv : v ∈ Λ) : ρ g v ∈ Λ :=
    ((StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ g.toGL).mp hg v).mpr hv
  have hΓb (g : H) (hg : g ∈ Γ) (v : E) (hv : v ∈ Submodule.span ℤ (Set.range b)) :
      ρ g v ∈ Submodule.span ℤ (Set.range b) := by
    rw [hb] at hv ⊢
    exact hΓ g hg v hv
  have hLstable : ∀ g ∈ Γ, ∀ z ∈ L, g • z ∈ (L : Set U) := by
    intro g hg z hz
    exact MultilinearAction.Construction.integralMultilinearCoordinates_covariant_stable ρ ρ b 1 Λ Γ hΓb hΓ hg hz
  have hMstable : ∀ g ∈ Γ, ∀ z ∈ M, g • z ∈ (M : Set D) := by
    intro g hg z hz
    exact MultilinearAction.Construction.integralMultilinearCoordinates_covariant_stable ρ τ b n Ω Γ hΓb
      (fun _ _ _ ha => ha) hg hz
  have hstab : (RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n)
      (Archimedean.Quotient.Construction.archimedeanRealRepresentation_det k n) b).range =
      (⨅ j, stabilizer H (x j)) ⊓ stabilizer H y := by
    ext g
    rw [RealSpecialLinearCoordinates.Construction.mem_realSpecialLinearCoordinates_range_iff, Archimedean.TensorStabilizer.Construction.archimedeanRealRepresentation_range_iff]
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf]
    change ((∀ j v, ρ g (mixedEmbedding.latticeBasis k j • v) = mixedEmbedding.latticeBasis k j • ρ g v) ∧
      (∀ v : Fin n → E, Matrix.det (Matrix.of (fun i => ρ g (v i))) = Matrix.det (Matrix.of v))) ↔
      ((∀ j, ρU g (x j) = x j) ∧ ρD g y = y)
    apply and_congr
    · exact (forall_congr' (fun j => AlgebraTensorForms.Construction.fixed_scalarUnaryForm_iff (R := ℝ) (A := mixedSpace k)
        (n := n) ρ b g (mixedEmbedding.latticeBasis k j))).symm
    · exact (AlgebraTensorForms.Construction.fixed_algebraDeterminantForm_iff (R := ℝ) (A := mixedSpace k) (n := n) ρ b g).symm
  change IsClosed ((QuotientGroup.mk : H → H ⧸ Γ) ''
    ((RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n)
      (Archimedean.Quotient.Construction.archimedeanRealRepresentation_det k n) b).range : Set H))
  rw [hstab]
  exact Finite.TensorClosedImage.Construction.stabilizer_image_closed_of_finite_tensors Γ x y L M
    (MultilinearAction.Construction.integralMultilinearCoordinates_closed b 1 Λ) (MultilinearAction.Construction.integralMultilinearCoordinates_closed b n Ω)
    (isDiscrete_iff_discreteTopology.mpr (MultilinearAction.Construction.integralMultilinearCoordinates_discrete b 1 Λ))
    (isDiscrete_iff_discreteTopology.mpr (MultilinearAction.Construction.integralMultilinearCoordinates_discrete b n Ω))
    hx hy hLstable hMstable

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.RealClosedImage.Construction
