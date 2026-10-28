import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterTriple
import OAI.RepresentationTheory.Theta.Geometric.TateComparison
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives

/-! # Minuscule Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters

noncomputable section

/-! The actual active minuscule raw operators and a normalized parameter
triple for every full character. This supplies the three symmetric-function
identities with multiplicities, before identifying the SL3 restriction. -/

open scoped Classical TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction OAI.RepresentationTheory.Theta.Geometric.TateComparison

/-- Descending chosen exponents, with similitude multiplier one and all other blocks
trivial: k=1 and k=2 are the two active GL3 minuscule cocharacters. -/
def activeMinusculeType {s : ℕ} (active : Fin s) (k : Fin 4) : AbelianScheme.TateComparison.Local.LocalType s where
  multiplier := 0
  exponent v i := if v = active ∧ i.val < k.val then 1 else 0
  dominant v i j hij := by
    dsimp
    by_cases hj : v = active ∧ j.val < k.val
    · have hi : v = active ∧ i.val < k.val := ⟨hj.1, lt_of_le_of_lt hij hj.2⟩
      simp only [ite_eq_left hj, ite_eq_left hi, le_refl]
    · simp only [ite_eq_right hj]
      split_ifs <;> norm_num

theorem activeMinusculeType_three {s : ℕ} (active : Fin s) :
    activeMinusculeType active 3 = AbelianScheme.CentralAction.CentralRepresentatives.Construction.centralType (AbelianScheme.CentralAction.CentralRepresentatives.Construction.t3Exponents active) 0 := by
  unfold activeMinusculeType AbelianScheme.CentralAction.CentralRepresentatives.Construction.centralType
  congr 1
  funext v i
  simp [AbelianScheme.CentralAction.CentralRepresentatives.Construction.t3Exponents]

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

/-- Actual raw characteristic functions supplied by TateComparison. -/
def nativeMinusculeHecke (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (k : Fin 4) : AbelianScheme.TateComparison.HeckeKernel.Hecke s q :=
  A.basis (activeMinusculeType D.reference.distinguished k)

theorem nativeMinusculeHecke_three (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (hA : A.IsRealization D hg hq hIsogenyQuotient) :
    nativeMinusculeHecke D A 3 = AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished := by
  rw [nativeMinusculeHecke, activeMinusculeType_three]
  exact (AbelianScheme.CentralAction.CentralRepresentatives.Construction.centralCoset_eq_basis s q A.basis hA.basis _ _).symm

theorem native_full_parameter_triple (F : Type*) [Field F] [CharZero F] [Algebra ℚ F]
    [IsAlgClosed F] (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (χ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F) :
    ∃ α : Fin 3 → F, (∀ i, α i ≠ 0) ∧
      χ (1 ⊗ₜ[ℚ] nativeMinusculeHecke D A 1) = (q : F) * (α 0 + α 1 + α 2) ∧
      χ (1 ⊗ₜ[ℚ] nativeMinusculeHecke D A 2) =
        (q : F) * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2) ∧
      χ (1 ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished) = α 0 * α 1 * α 2 := by
  have hu : IsUnit (AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished) := Units.isUnit _
  have huF : IsUnit ((1 : F) ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished) :=
    hu.map (Algebra.TensorProduct.includeRight : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q)
  exact ParameterTriple.Central.exists_normalized_parameter_triple (q : F)
    (χ (1 ⊗ₜ[ℚ] nativeMinusculeHecke D A 1))
    (χ (1 ⊗ₜ[ℚ] nativeMinusculeHecke D A 2))
    (χ (1 ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished))
    (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) (huF.map χ).ne_zero

/-- One choice from the actual cubic, retaining its root multiplicities. -/
def nativeFullParameterTriple (F : Type*) [Field F] [CharZero F] [Algebra ℚ F]
    [IsAlgClosed F] (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (χ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F) : Fin 3 → F :=
  Classical.choose (native_full_parameter_triple D F A χ)

theorem nativeFullParameterTriple_spec (F : Type*) [Field F] [CharZero F] [Algebra ℚ F]
    [IsAlgClosed F] (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (χ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F) :
    let α := nativeFullParameterTriple D F A χ
    (∀ i, α i ≠ 0) ∧
      χ (1 ⊗ₜ[ℚ] nativeMinusculeHecke D A 1) = (q : F) * (α 0 + α 1 + α 2) ∧
      χ (1 ⊗ₜ[ℚ] nativeMinusculeHecke D A 2) =
        (q : F) * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2) ∧
      χ (1 ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished) = α 0 * α 1 * α 2 :=
  Classical.choose_spec (native_full_parameter_triple D F A χ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters
