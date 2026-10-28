import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteConjugation
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteIntegralGenerators

/-! # Finite Masked Generators -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization

noncomputable section

section

/-! Retain a set of finite places and put the identity at all other places. -/

open scoped Classical _root_.Matrix
open _root_.Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

def finitePlaceIdempotent (S : Set (HeightOneSpectrum ℤ)) : Theta.PoissonAutomorphyNormalizationData.AQf :=
  (Theta.IntegralAdeles.PoissonAutomorphyConstruction.integralProductHomeomorph (fun v => if v ∈ S then 1 else 0)).val

theorem finitePlaceIdempotent_eval (S : Set (HeightOneSpectrum ℤ)) (v : HeightOneSpectrum ℤ) :
    FiniteSchur.Realization.finitePrimeEval v (finitePlaceIdempotent S) = if v ∈ S then 1 else 0 := by
  change (↑(if v ∈ S then (1 : v.adicCompletionIntegers ℚ) else 0) : v.adicCompletion ℚ) = _
  by_cases hv : v ∈ S <;> simp [hv]

def finitePlaceMask (S : Set (HeightOneSpectrum ℤ)) (a : Theta.PoissonAutomorphyNormalizationData.AQf) : Theta.PoissonAutomorphyNormalizationData.AQf :=
  finitePlaceIdempotent S * a

theorem finitePlaceMask_eval (S : Set (HeightOneSpectrum ℤ)) (v : HeightOneSpectrum ℤ) (a : Theta.PoissonAutomorphyNormalizationData.AQf) :
    FiniteSchur.Realization.finitePrimeEval v (finitePlaceMask S a) = if v ∈ S then FiniteSchur.Realization.finitePrimeEval v a else 0 := by
  unfold finitePlaceMask
  rw [map_mul, finitePlaceIdempotent_eval]
  by_cases hv : v ∈ S <;> simp [hv]

theorem finitePlaceMask_integral {S : Set (HeightOneSpectrum ℤ)} {a : Theta.PoissonAutomorphyNormalizationData.AQf}
    (ha : ∀ v ∈ S, a v ∈ v.adicCompletionIntegers ℚ) : finitePlaceMask S a ∈ Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
  intro v
  change FiniteSchur.Realization.finitePrimeEval v (finitePlaceMask S a) ∈ v.adicCompletionIntegers ℚ
  rw [finitePlaceMask_eval]
  by_cases hv : v ∈ S
  · rw [ite_eq_left hv]
    exact ha v hv
  · simp only [ite_eq_right hv, zero_mem]

variable {κ : Type*} [DecidableEq κ]

def finiteMaskMatrix (S : Set (HeightOneSpectrum ℤ)) (A : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i j => (1 : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) i j + finitePlaceMask S (A i j - (1 : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) i j)

theorem finiteMaskMatrix_eval (S : Set (HeightOneSpectrum ℤ)) (A : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf)
    (v : HeightOneSpectrum ℤ) :
    (finiteMaskMatrix S A).map (FiniteSchur.Realization.finitePrimeEval v) = if v ∈ S then A.map (FiniteSchur.Realization.finitePrimeEval v) else 1 := by
  apply Matrix.ext
  intro i j
  change FiniteSchur.Realization.finitePrimeEval v ((1 : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) i j +
    finitePlaceMask S (A i j - (1 : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) i j)) = _
  rw [map_add, finitePlaceMask_eval, map_sub, FiniteConjugation.Realization.finitePrimeEval_matrix_one]
  by_cases hv : v ∈ S <;> simp [hv]

theorem finiteMaskMatrix_one (S : Set (HeightOneSpectrum ℤ)) :
    finiteMaskMatrix S (1 : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) = 1 := by
  apply FiniteConjugation.Realization.finiteMatrix_ext
  intro v
  rw [finiteMaskMatrix_eval]
  by_cases hv : v ∈ S <;> simp [hv]

variable [Fintype κ]

theorem finiteMaskMatrix_mul (S : Set (HeightOneSpectrum ℤ)) (A B : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) :
    finiteMaskMatrix S (A * B) = finiteMaskMatrix S A * finiteMaskMatrix S B := by
  apply FiniteConjugation.Realization.finiteMatrix_ext
  intro v
  rw [Matrix.map_mul, finiteMaskMatrix_eval, finiteMaskMatrix_eval, finiteMaskMatrix_eval,
    Matrix.map_mul]
  by_cases hv : v ∈ S <;> simp [hv]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteMaskMatrix_symplectic (S : Set (HeightOneSpectrum ℤ)) (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) :
    finiteMaskMatrix S g.val ∈ Matrix.symplecticGroup ι Theta.PoissonAutomorphyNormalizationData.AQf := by
  apply SymplecticGroup.mem_iff'.mpr
  apply FiniteConjugation.Realization.finiteMatrix_ext
  intro v
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_J, finiteMaskMatrix_eval]
  by_cases hv : v ∈ S
  · simp only [ite_eq_left hv]
    exact SymplecticGroup.mem_iff'.mp (SymplecticGroup.map_mem g.property (FiniteSchur.Realization.finitePrimeEval v))
  · simp only [ite_eq_right hv, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

def finiteMaskSymplectic (S : Set (HeightOneSpectrum ℤ)) : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf →* Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf where
  toFun g := ⟨finiteMaskMatrix S g.val, finiteMaskMatrix_symplectic S g⟩
  map_one' := Subtype.ext (finiteMaskMatrix_one S)
  map_mul' g h := Subtype.ext (finiteMaskMatrix_mul S g.val h.val)

theorem finiteMaskSymplectic_projection (S : Set (HeightOneSpectrum ℤ)) (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf)
    (v : HeightOneSpectrum ℤ) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) (finiteMaskSymplectic S g) =
      if v ∈ S then Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) g else 1 := by
  apply Subtype.ext
  change (finiteMaskMatrix S g.val).map (FiniteSchur.Realization.finitePrimeEval v) = _
  rw [finiteMaskMatrix_eval]
  by_cases hv : v ∈ S <;> simp [hv, Theta.PoissonAutomorphyNormalizationData.mapSp]

theorem finiteMaskSymplectic_partition (S : Set (HeightOneSpectrum ℤ)) (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) :
    finiteMaskSymplectic S g * finiteMaskSymplectic Sᶜ g = g := by
  apply Subtype.ext
  apply FiniteConjugation.Realization.finiteMatrix_ext
  intro v
  change (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) (finiteMaskSymplectic S g * finiteMaskSymplectic Sᶜ g)).val = _
  rw [map_mul, finiteMaskSymplectic_projection, finiteMaskSymplectic_projection]
  by_cases hv : v ∈ S <;> simp [hv, Theta.PoissonAutomorphyNormalizationData.mapSp]

end

/-! A finite exceptional set makes retained unipotent coefficients integral. -/

open scoped Classical _root_.Matrix
open _root_.Matrix Filter IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem map_ringUpper {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (B : Matrix ι ι K) (hB : B.IsSymm) :
    Theta.PoissonAutomorphyNormalizationData.mapSp f (QuadraticCommutator.Realization.ringUpper B hB) = QuadraticCommutator.Realization.ringUpper (B.map f) (hB.map f) := by
  apply Subtype.ext
  change (Matrix.fromBlocks (1 : Matrix ι ι K) B 0 1).map f =
    Matrix.fromBlocks 1 (B.map f) 0 1
  simp [Matrix.fromBlocks_map]

theorem map_ringLower {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (B : Matrix ι ι K) (hB : B.IsSymm) :
    Theta.PoissonAutomorphyNormalizationData.mapSp f (RingWeyl.Realization.ringLower K B hB) = RingWeyl.Realization.ringLower L (B.map f) (hB.map f) := by
  apply Subtype.ext
  change (Matrix.fromBlocks (1 : Matrix ι ι K) 0 B 1).map f =
    Matrix.fromBlocks 1 0 (B.map f) 1
  simp [Matrix.fromBlocks_map]

def finiteMaskCoefficients (S : Set (HeightOneSpectrum ℤ)) (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i j => finitePlaceMask S (B i j)

omit [Fintype ι] [DecidableEq ι] in
theorem finiteMaskCoefficients_symmetric (S : Set (HeightOneSpectrum ℤ))
    (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) : (finiteMaskCoefficients S B).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact congrArg (finitePlaceMask S) (hB.apply i j)

theorem finiteMaskSymplectic_upper (S : Set (HeightOneSpectrum ℤ))
    (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    finiteMaskSymplectic S (QuadraticCommutator.Realization.ringUpper B hB) =
      QuadraticCommutator.Realization.ringUpper (finiteMaskCoefficients S B) (finiteMaskCoefficients_symmetric S B hB) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [finiteMaskSymplectic, finiteMaskMatrix, QuadraticCommutator.Realization.ringUpper, finiteMaskCoefficients,
      finitePlaceMask, Matrix.fromBlocks, Matrix.one_apply]

theorem finiteMaskSymplectic_lower (S : Set (HeightOneSpectrum ℤ))
    (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    finiteMaskSymplectic S (RingWeyl.Realization.ringLower Theta.PoissonAutomorphyNormalizationData.AQf B hB) =
      RingWeyl.Realization.ringLower Theta.PoissonAutomorphyNormalizationData.AQf (finiteMaskCoefficients S B) (finiteMaskCoefficients_symmetric S B hB) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [finiteMaskSymplectic, finiteMaskMatrix, RingWeyl.Realization.ringLower, finiteMaskCoefficients,
      finitePlaceMask, Matrix.fromBlocks, Matrix.one_apply]

omit [DecidableEq ι] in
theorem exists_finite_mask_integral_coefficients (B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ T : Finset (HeightOneSpectrum ℤ), S ⊆ T →
      FiniteIntegralQuadratic.Realization.HalfIntegralMatrix (finiteMaskCoefficients (T : Set (HeightOneSpectrum ℤ))ᶜ B) := by
  have hevent : ∀ᶠ v : HeightOneSpectrum ℤ in cofinite,
      ∀ i j, (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j) v ∈ v.adicCompletionIntegers ℚ := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j).property
  have hfinite := Filter.eventually_cofinite.mp hevent
  refine ⟨hfinite.toFinset, ?_⟩
  intro T hST i j
  have heq : algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) *
      finiteMaskCoefficients (T : Set (HeightOneSpectrum ℤ))ᶜ B i j =
      finitePlaceMask (T : Set (HeightOneSpectrum ℤ))ᶜ (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j) := by
    unfold finiteMaskCoefficients finitePlaceMask
    ring
  rw [heq]
  apply finitePlaceMask_integral
  intro v hv
  have hvS : v ∉ hfinite.toFinset := fun h => hv (hST h)
  have hall : ∀ i j, (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j) v ∈ v.adicCompletionIntegers ℚ := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hvS
  exact hall i j

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteMaskedGenerators.Realization
