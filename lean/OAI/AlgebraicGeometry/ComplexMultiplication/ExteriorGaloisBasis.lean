import OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorBaseChange
import OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorBasisPermutation
import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisEmbeddingBasis

/-! # Exterior Galois Basis -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorGaloisBasis.CM.CMDecomposition

noncomputable section

/-!
# Exterior monomial bases and scalar Galois orbits

The exterior basis is built on the scalar extension of the actual rational
exterior power. Its coefficients embed into the complex exterior power,
and scalar Galois conjugation permutes its basis lines with nonzero
multipliers. Rational vectors therefore have Galois-stable monomial support.
-/

open scoped TensorProduct Classical

private def baseChangedExteriorBasis {K V ι : Type*} [Field K] [Algebra ℚ K]
    [AddCommGroup V] [Module ℚ V] [LinearOrder ι]
    (b : Module.Basis ι K (K ⊗[ℚ] V)) (n : ℕ) :
    Module.Basis (Set.powersetCard ι n) K (K ⊗[ℚ] (⋀[ℚ]^n V)) :=
  (b.exteriorPower n).map (ExteriorBaseChange.CM.exteriorBaseChangeEquiv K V n).symm

private theorem coefficientInclusion_exteriorProduct (K : IntermediateField ℚ ℂ)
    (V : Type*) [AddCommGroup V] [Module ℚ V] (n : ℕ) (v : Fin n → K ⊗[ℚ] V) :
    EmbeddingCoefficientField.CM.coefficientInclusion K (⋀[ℚ]^n V)
      ((ExteriorBaseChange.CM.exteriorBaseChangeEquiv K V n).symm (exteriorPower.ιMulti K n v)) =
    (ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ V n).symm
      (exteriorPower.ιMulti ℂ n (fun i => EmbeddingCoefficientField.CM.coefficientInclusion K V (v i))) :=
  ExteriorBaseChange.CM.coefficientMap_exteriorProduct K V n K.val v

private theorem baseChangedExteriorBasis_permuted {K V ι : Type*}
    [Field K] [Algebra ℚ K] [AddCommGroup V] [Module ℚ V] [LinearOrder ι]
    (b : Module.Basis ι K (K ⊗[ℚ] V)) (n : ℕ) (e : Equiv.Perm ι)
    (s : Set.powersetCard ι n) :
    (ExteriorBaseChange.CM.exteriorBaseChangeEquiv K V n).symm (ExteriorBasisPermutation.CM.permutedExteriorVector n b e s) =
      (b.exteriorPower n).repr (ExteriorBasisPermutation.CM.permutedExteriorVector n b e s)
        (ExteriorBasisPermutation.CM.exteriorIndexPermutation n e s) •
      baseChangedExteriorBasis b n (ExteriorBasisPermutation.CM.exteriorIndexPermutation n e s) := by
  have h := congrArg (ExteriorBaseChange.CM.exteriorBaseChangeEquiv K V n).symm
    (ExteriorBasisPermutation.CM.permutedExteriorVector_eq_smul n b e s)
  simpa only [map_smul, baseChangedExteriorBasis, Module.Basis.map_apply] using h

private theorem scalarConjugate_baseChangedExteriorBasis {K V ι : Type*}
    [Field K] [Algebra ℚ K] [AddCommGroup V] [Module ℚ V] [LinearOrder ι]
    (b : Module.Basis ι K (K ⊗[ℚ] V)) (n : ℕ) (g : Gal(K/ℚ)) (e : Equiv.Perm ι)
    (hb : ∀ i, ScalarDescent.CM.scalarConjugate ℚ K V g (b i) = b (e i)) (s : Set.powersetCard ι n) :
    ScalarDescent.CM.scalarConjugate ℚ K (⋀[ℚ]^n V) g (baseChangedExteriorBasis b n s) =
      (b.exteriorPower n).repr (ExteriorBasisPermutation.CM.permutedExteriorVector n b e s)
        (ExteriorBasisPermutation.CM.exteriorIndexPermutation n e s) •
      baseChangedExteriorBasis b n (ExteriorBasisPermutation.CM.exteriorIndexPermutation n e s) := by
  have happly : baseChangedExteriorBasis b n s =
      (ExteriorBaseChange.CM.exteriorBaseChangeEquiv K V n).symm (exteriorPower.ιMulti K n
        (fun i => b (Set.powersetCard.ofFinEmbEquiv.symm s i))) := by
    simp only [baseChangedExteriorBasis, Module.Basis.map_apply, exteriorPower.basis_apply,
      exteriorPower.ιMulti_family, Function.comp_def]
  rw [happly, ExteriorBaseChange.CM.scalarConjugate_exteriorProduct]
  simp_rw [hb]
  exact baseChangedExteriorBasis_permuted b n e s

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {H : WeightOne.CM.WeightOneHodgeStructure U} (D : Decomposition.CM.CMDecomposition H) (n : ℕ)

local instance : LinearOrder D.EmbeddingIndex := linearOrderOfSTO WellOrderingRel

/-- An exterior basis is indexed by subsets of distinct degree-one embedding indices. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.ExteriorIndex := Set.powersetCard D.EmbeddingIndex n

instance _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.exteriorIndexFintype : Fintype (D.ExteriorIndex n) :=
  inferInstanceAs (Fintype (Set.powersetCard D.EmbeddingIndex n))

/-- Exterior embedding basis over the finite common field, on the rational exterior power. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.exteriorEmbeddingBasis : Module.Basis (D.ExteriorIndex n) D.commonCoefficientField
    (D.commonCoefficientField ⊗[ℚ] (⋀[ℚ]^n U)) :=
  baseChangedExteriorBasis D.coefficientEmbeddingBasis n

/-- The corresponding exterior basis on the complexification of the rational exterior power. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.complexExteriorEmbeddingBasis : Module.Basis (D.ExteriorIndex n) ℂ
    (WeightOne.CM.Complexification (⋀[ℚ]^n U)) :=
  (D.embeddingBasis.exteriorPower n).map (ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ U n).symm

/-- A wedge monomial in any order, including zero monomials with repeated indices. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.exteriorMonomial (j : Fin n → D.EmbeddingIndex) :
    D.commonCoefficientField ⊗[ℚ] (⋀[ℚ]^n U) :=
  (ExteriorBaseChange.CM.exteriorBaseChangeEquiv D.commonCoefficientField U n).symm
    (exteriorPower.ιMulti D.commonCoefficientField n (fun i => D.coefficientEmbeddingBasis (j i)))

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.exteriorEmbeddingBasis_apply (s : D.ExteriorIndex n) :
    D.exteriorEmbeddingBasis n s = D.exteriorMonomial n (Set.powersetCard.ofFinEmbEquiv.symm s) := by
  unfold Decomposition.CM.CMDecomposition.exteriorMonomial Decomposition.CM.CMDecomposition.exteriorEmbeddingBasis baseChangedExteriorBasis
  simp only [Module.Basis.map_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, Function.comp_def]

/-- The coefficient-field basis maps to the corresponding complex exterior basis. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.coefficientInclusion_exteriorEmbeddingBasis (s : D.ExteriorIndex n) :
    EmbeddingCoefficientField.CM.coefficientInclusion D.commonCoefficientField (⋀[ℚ]^n U) (D.exteriorEmbeddingBasis n s) =
      D.complexExteriorEmbeddingBasis n s := by
  rw [D.exteriorEmbeddingBasis_apply]
  simp only [Decomposition.CM.CMDecomposition.exteriorMonomial]
  rw [coefficientInclusion_exteriorProduct]
  simp_rw [D.coefficientInclusion_embeddingBasis]
  unfold Decomposition.CM.CMDecomposition.complexExteriorEmbeddingBasis
  simp only [Module.Basis.map_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, Function.comp_def]

/-- Scalar Galois conjugation acts factor by factor on exterior monomials. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.scalarConjugate_exteriorMonomial (g : Gal(D.commonCoefficientField/ℚ))
    (j : Fin n → D.EmbeddingIndex) :
    ScalarDescent.CM.scalarConjugate ℚ D.commonCoefficientField (⋀[ℚ]^n U) g (D.exteriorMonomial n j) =
      D.exteriorMonomial n (fun i => D.galoisIndex g (j i)) := by
  simp only [Decomposition.CM.CMDecomposition.exteriorMonomial]
  rw [ExteriorBaseChange.CM.scalarConjugate_exteriorProduct]
  simp only [D.scalarConjugate_coefficientEmbeddingBasis]

/-- The induced permutation of exterior-basis index subsets. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.galoisExteriorIndex (g : Gal(D.commonCoefficientField/ℚ)) : Equiv.Perm (D.ExteriorIndex n) :=
  ExteriorBasisPermutation.CM.exteriorIndexPermutation n (D.galoisIndexEquiv g)

/-- The multiplier contributed by reordering the conjugated wedge factors. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.exteriorGaloisFactor (g : Gal(D.commonCoefficientField/ℚ)) (s : D.ExteriorIndex n) :
    D.commonCoefficientField :=
  (D.coefficientEmbeddingBasis.exteriorPower n).repr
    (ExteriorBasisPermutation.CM.permutedExteriorVector n D.coefficientEmbeddingBasis (D.galoisIndexEquiv g) s)
      (D.galoisExteriorIndex n g s)

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.exteriorGaloisFactor_ne_zero (g : Gal(D.commonCoefficientField/ℚ))
    (s : D.ExteriorIndex n) : D.exteriorGaloisFactor n g s ≠ 0 :=
  ExteriorBasisPermutation.CM.permutedExteriorVector_coordinate_ne_zero n D.coefficientEmbeddingBasis (D.galoisIndexEquiv g) s

private theorem galoisIndexEquiv_apply_normalized (g : Gal(D.commonCoefficientField/ℚ))
    (i : D.EmbeddingIndex) : D.galoisIndexEquiv g i = D.galoisIndex g i := rfl

private theorem coefficientBasis_action_normalized (g : Gal(D.commonCoefficientField/ℚ))
    (i : D.EmbeddingIndex) :
    ScalarDescent.CM.scalarConjugate ℚ D.commonCoefficientField U g (D.coefficientEmbeddingBasis i) =
      D.coefficientEmbeddingBasis (D.galoisIndexEquiv g i) := by
  rw [galoisIndexEquiv_apply_normalized]
  exact D.scalarConjugate_coefficientEmbeddingBasis g i

/-- Each exterior-basis line is sent to its Galois-conjugate line with a nonzero multiplier. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.scalarConjugate_exteriorEmbeddingBasis (g : Gal(D.commonCoefficientField/ℚ))
    (s : D.ExteriorIndex n) :
    ScalarDescent.CM.scalarConjugate ℚ D.commonCoefficientField (⋀[ℚ]^n U) g (D.exteriorEmbeddingBasis n s) =
      D.exteriorGaloisFactor n g s • D.exteriorEmbeddingBasis n (D.galoisExteriorIndex n g s) := by
  rw [D.exteriorEmbeddingBasis_apply, D.scalarConjugate_exteriorMonomial]
  unfold Decomposition.CM.CMDecomposition.exteriorMonomial Decomposition.CM.CMDecomposition.exteriorGaloisFactor Decomposition.CM.CMDecomposition.galoisExteriorIndex Decomposition.CM.CMDecomposition.exteriorEmbeddingBasis
  have h := baseChangedExteriorBasis_permuted D.coefficientEmbeddingBasis n
    (D.galoisIndexEquiv g) s
  unfold ExteriorBasisPermutation.CM.permutedExteriorVector at h ⊢
  simp only [galoisIndexEquiv_apply_normalized] at h ⊢
  -- Reuse the proved equality without repeating the elaborator's expensive conversion.
  -- Lean's kernel checks the resulting proof term against the stated equality.
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    for d in (← Lean.getLCtx) do
      if d.userName == `h then
        goal.assign (.fvar d.fvarId)
        Lean.Elab.Tactic.replaceMainGoal []
        return
    throwError "local equality proof not found"

/-- Exterior coordinates transform by the field automorphism and the reordering multiplier. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.exteriorEmbeddingBasis_repr_scalarConjugate (g : Gal(D.commonCoefficientField/ℚ))
    (x : D.commonCoefficientField ⊗[ℚ] (⋀[ℚ]^n U)) (s : D.ExteriorIndex n) :
    (D.exteriorEmbeddingBasis n).repr
        (ScalarDescent.CM.scalarConjugate ℚ D.commonCoefficientField (⋀[ℚ]^n U) g x) (D.galoisExteriorIndex n g s) =
      g ((D.exteriorEmbeddingBasis n).repr x s) * D.exteriorGaloisFactor n g s := by
  have hs : ScalarDescent.CM.scalarConjugate ℚ D.commonCoefficientField (⋀[ℚ]^n U) g x =
      ∑ t, (g ((D.exteriorEmbeddingBasis n).repr x t) * D.exteriorGaloisFactor n g t) •
        D.exteriorEmbeddingBasis n (D.galoisExteriorIndex n g t) := by
    conv_lhs => rw [← (D.exteriorEmbeddingBasis n).sum_repr x]
    simp only [map_sum, ScalarDescent.CM.scalarConjugate_smul, D.scalarConjugate_exteriorEmbeddingBasis,
      smul_smul]
  rw [hs]
  simp [Finsupp.single_apply, (D.galoisExteriorIndex n g).injective.eq_iff]

/-- Rational exterior classes have nonzero coefficients on entire Galois orbits. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.rational_exterior_coefficient_ne_zero_iff (g : Gal(D.commonCoefficientField/ℚ))
    (u : ⋀[ℚ]^n U) (s : D.ExteriorIndex n) :
    (D.exteriorEmbeddingBasis n).repr ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] u)
        (D.galoisExteriorIndex n g s) ≠ 0 ↔
      (D.exteriorEmbeddingBasis n).repr ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] u) s ≠ 0 := by
  have he := D.exteriorEmbeddingBasis_repr_scalarConjugate n g
    ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] u) s
  simp only [ScalarDescent.CM.scalarConjugate_tmul, map_one] at he
  rw [he]
  exact (mul_ne_zero_iff).trans
    ⟨fun hh => (map_ne_zero_iff g g.injective).mp hh.1,
      fun hh => ⟨(map_ne_zero_iff g g.injective).mpr hh, D.exteriorGaloisFactor_ne_zero n g s⟩⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorGaloisBasis.CM.CMDecomposition
