import OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizedRationalFamilies
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalGraphPositive
import OAI.RepresentationTheory.Weil.AdelicSplitting.CompatibilityReduction

/-! # Rational Compatibility -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RationalCompatibility.Construction

noncomputable section

/-! Positive theta multipliers identify the normalized rational unitary
operators with the actual rational symplectic graph. -/

open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

include hN D in
theorem positive_global_lifts_equal (a b : Vacuum.Construction.GlobalCover F (n * m) C.ψ)
    (ha : a ∈ PositiveScalarProduct.Construction.globalPositiveThetaSubgroup F (n * m) C.ψ)
    (hb : b ∈ PositiveScalarProduct.Construction.globalPositiveThetaSubgroup F (n * m) C.ψ)
    (hp : Vacuum.Construction.globalProjection F (n * m) C.ψ a = Vacuum.Construction.globalProjection F (n * m) C.ψ b) : a = b := by
  apply mul_inv_eq_one.mp
  let w : ArchimedeanAdeles.Construction.Places F := .inl (Classical.choice (inferInstance : Nonempty (NumberField.InfinitePlace F)))
  apply PositiveScalarProduct.Construction.globalPositiveTheta_scalar_eq_one F (n * m) C.ψ w (a * b⁻¹)
    ((PositiveScalarProduct.Construction.globalPositiveThetaSubgroup F (n * m) C.ψ).mul_mem ha
      ((PositiveScalarProduct.Construction.globalPositiveThetaSubgroup F (n * m) C.ψ).inv_mem hb))
  apply GlobalKernel.Construction.normalized_globalProjection_kernel_circle F d hd n m hN H K C P D w
  rw [map_mul, map_inv, hp, mul_inv_cancel]

include hN D in
theorem normalizedRationalFamily_mem_graph_of_positive
    (r : Local.FunctionsMetaplectic.Construction.Symplectic F (n * m) →* Vacuum.Construction.GlobalCover F (n * m) C.ψ)
    (hr : ∀ γ a, (γ, a) ∈ Rational.Construction.rationalGraph F (n * m) C.ψ ↔ r γ = a)
    (hcover : ∀ γ, Vacuum.Construction.globalProjection F (n * m) C.ψ (r γ) = Vacuum.Construction.rationalSymplectic F (n * m) γ)
    (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val)
    (hpos : NormalizedRationalFamilies.Construction.normalizedRationalFamily F d hd n m H K C P D g ∈ TestFamilyAction.Construction.positiveThetaSubgroup F (n * m) C.ψ) :
    g ∈ CompatibilityReduction.Construction.rationalCompatibilityLocus F d hd n m H K C P D := by
  let γ := TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g
  have hrgraph : (γ, r γ) ∈ Rational.Construction.rationalGraph F (n * m) C.ψ := (hr γ (r γ)).mpr rfl
  have hrpos : r γ ∈ PositiveScalarProduct.Construction.globalPositiveThetaSubgroup F (n * m) C.ψ :=
    RationalGraphPositive.Construction.normalized_rationalGraph_positive F d hd n m hN H K C P D hrgraph
  have hapos : Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Integral.Construction.rationalPair F H.val K.val g) ∈
      PositiveScalarProduct.Construction.globalPositiveThetaSubgroup F (n * m) C.ψ :=
    ⟨NormalizedRationalFamilies.Construction.normalizedRationalFamily F d hd n m H K C P D g, hpos, NormalizedRationalFamilies.Construction.normalizedRationalFamily_assemble F d hd n m H K C P D g⟩
  have he := positive_global_lifts_equal F d hd n m hN H K C P D _ _ hapos hrpos
    ((BaseChange.Construction.constructedAdelicLift_rational_covers F d n m H K P hd C D g).trans (hcover γ).symm)
  exact (hr γ _).mpr he.symm

include hN D in
theorem normalized_rational_compatibility (hns : ¬ IsSquare d)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val) :
    ∃ r : Local.FunctionsMetaplectic.Construction.Symplectic F (n * m) →* Vacuum.Construction.GlobalCover F (n * m) C.ψ,
      (∀ γ a, (γ, a) ∈ Rational.Construction.rationalGraph F (n * m) C.ψ ↔ r γ = a) ∧
      (∀ γ, Vacuum.Construction.globalProjection F (n * m) C.ψ (r γ) = Vacuum.Construction.rationalSymplectic F (n * m) γ) ∧
      ∀ g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val,
        Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Integral.Construction.rationalPair F H.val K.val g) =
          r (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g) := by
  obtain ⟨r, hr, hcover⟩ := RationalGraphPositive.Construction.normalized_rationalGraph_realization F d hd n m hN H K C P D hns hH hK
  refine ⟨r, hr, hcover, ?_⟩
  apply CompatibilityReduction.Construction.rational_compatibility_of_graph_and_open_cells F d hd n m H K C P D hns r hr
  · intro g hg
    exact normalizedRationalFamily_mem_graph_of_positive F d hd n m hN H K C P D r hr hcover (g, 1)
      (NormalizedRationalFamilies.Construction.normalized_firstFactor_positive F d hd hns n m hN H K hH hK C P D g hg)
  · intro g hg
    exact normalizedRationalFamily_mem_graph_of_positive F d hd n m hN H K C P D r hr hcover (1, g)
      (NormalizedRationalFamilies.Construction.normalized_secondFactor_positive F d hd hns n m hN H K hH hK C P D g hg)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RationalCompatibility.Construction
