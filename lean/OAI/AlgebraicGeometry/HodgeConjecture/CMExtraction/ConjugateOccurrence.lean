import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterConjugation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CentralFinite
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CharacterRefinement
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity
import OAI.AlgebraicGeometry.ComplexMultiplication.ScalarDescent

/-! # Conjugate Occurrence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ConjugateOccurrence

noncomputable section

/-! Coefficient conjugation carries the whole full native generalized
Hecke eigenspace to the conjugate character's space. Occurrence is thus
preserved on the actual rational Betti representation. -/

open scoped TensorProduct

namespace Spectral
open OAI.AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors

variable {F U : Type*} [Field F] [Algebra ℚ F] [AddCommGroup U] [Module ℚ U]

theorem coefficientConjugate_inverse (σ : F ≃ₐ[ℚ] F) (x : F ⊗[ℚ] U) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F U σ.symm (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F U σ x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul c u => simp only [ComplexMultiplication.ScalarDescent.CM.scalarConjugate_tmul, σ.symm_apply_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coefficientConjugate_baseChange (σ : F ≃ₐ[ℚ] F) (T : Module.End ℚ U)
    (x : F ⊗[ℚ] U) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F U σ (T.baseChange F x) = T.baseChange F (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F U σ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c u => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coefficientConjugate_shift_power (σ : F ≃ₐ[ℚ] F) (T : Module.End ℚ U)
    (a : F) (n : ℕ) (x : F ⊗[ℚ] U) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F U σ (((T.baseChange F - a • 1) ^ n) x) =
      ((T.baseChange F - σ a • 1) ^ n) (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F U σ x) := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ n hn =>
    simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_sub,
      coefficientConjugate_baseChange, ComplexMultiplication.ScalarDescent.CM.scalarConjugate_smul, hn]

theorem coefficientConjugate_jointSpace {J : Type*} (T : J → Module.End ℚ U)
    (χ : J → F) (σ : F ≃ₐ[ℚ] F) {x : F ⊗[ℚ] U}
    (hx : x ∈ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange F) χ) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F U σ x ∈ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange F) (fun h => σ (χ h)) := by
  simp only [HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace, Submodule.mem_iInf] at hx ⊢
  intro h
  obtain ⟨n, hn, hx⟩ := Module.End.mem_genEigenspace.mp (hx h)
  refine Module.End.mem_genEigenspace.mpr ⟨n, hn, ?_⟩
  change (((T h).baseChange F - σ (χ h) • 1) ^ n) (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F U σ x) = 0
  rw [← coefficientConjugate_shift_power, LinearMap.mem_ker.mp hx, map_zero]

end Spectral

namespace Intrinsic
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterConjugation.Central
open OAI.AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ConjugateOccurrence.Spectral

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  (F : Type*) [Field F] [Algebra ℚ F] (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)

include hElementaryDivisors in
theorem native_conjugate_full_mem (χ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F) (σ : F ≃ₐ[ℚ] F)
    {x : F ⊗[ℚ] D.H1} (hx : x ∈ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (Intrinsic.CentralFinite.nativeFullHeckeActionOver D F A) χ) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F D.H1 σ x ∈ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (Intrinsic.CentralFinite.nativeFullHeckeActionOver D F A)
      (Intrinsic.ParameterConjugation.Central.conjugateFullCharacter (F := F) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ) := by
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :=
    { (inferInstance : Ring (AbelianScheme.TateComparison.HeckeKernel.Hecke s q)) with mul_comm := AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q hElementaryDivisors }
  rw [CharacterRefinement.Spectral.jointSpace_scalar_extension] at hx ⊢
  simp only [Intrinsic.CentralFinite.nativeFullHeckeActionOver_tmul, one_smul, Intrinsic.ParameterConjugation.Central.conjugateFullCharacter_one_tmul] at hx ⊢
  exact Spectral.coefficientConjugate_jointSpace A.cohomologyAction (fun h => χ (1 ⊗ₜ[ℚ] h)) σ hx

include hElementaryDivisors in
theorem native_conjugate_full_space (χ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F) (σ : F ≃ₐ[ℚ] F) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F D.H1 σ '' (HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (Intrinsic.CentralFinite.nativeFullHeckeActionOver D F A) χ : Set _) =
      (HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (Intrinsic.CentralFinite.nativeFullHeckeActionOver D F A)
        (Intrinsic.ParameterConjugation.Central.conjugateFullCharacter (F := F) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ) : Set _) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact native_conjugate_full_mem D hElementaryDivisors F A χ σ hx
  · intro y hy
    refine ⟨ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F D.H1 σ.symm y, ?_, ?_⟩
    · have hm := native_conjugate_full_mem D hElementaryDivisors F A
        (Intrinsic.ParameterConjugation.Central.conjugateFullCharacter (F := F) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ) σ.symm hy
      change ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F D.H1 σ.symm y ∈ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (Intrinsic.CentralFinite.nativeFullHeckeActionOver D F A) χ
      simpa only [Intrinsic.ParameterConjugation.Central.conjugateFullCharacter_inverse] using hm
    · exact Spectral.coefficientConjugate_inverse σ.symm y

include hElementaryDivisors in
theorem native_conjugate_full_occurs (χ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F) (σ : F ≃ₐ[ℚ] F)
    (hχ : HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (Intrinsic.CentralFinite.nativeFullHeckeActionOver D F A) χ ≠ ⊥) :
    HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (Intrinsic.CentralFinite.nativeFullHeckeActionOver D F A)
      (Intrinsic.ParameterConjugation.Central.conjugateFullCharacter (F := F) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F D.H1 σ x, native_conjugate_full_mem D hElementaryDivisors F A χ σ hx, ?_⟩
  intro hz
  have h := congrArg (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ F D.H1 σ.symm) hz
  rw [Spectral.coefficientConjugate_inverse, map_zero] at h
  exact hx0 h

end Intrinsic

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ConjugateOccurrence
