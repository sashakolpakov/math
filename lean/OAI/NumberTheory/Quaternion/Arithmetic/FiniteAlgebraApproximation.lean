import OAI.NumberTheory.Quaternion.Arithmetic.UnitsWeakApproximation

/-! # Finite Algebra Approximation -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteAlgebraApproximation

noncomputable section

/-! Simultaneous approximation in local scalar extensions of a finite
algebra, expressed through compatible bases. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set

variable {F : Type*} [Field F] [NumberField F] {ι : Type*} [Fintype ι]
  (v : ι → HeightOneSpectrum (𝓞 F))
  {A : Type*} [Ring A] [Algebra F A]
  {C : ι → Type*} [∀ i, Ring (C i)] [∀ i, Algebra F (C i)]
  [∀ i, Algebra ((v i).adicCompletion F) (C i)]
  [∀ i, IsScalarTower F ((v i).adicCompletion F) (C i)]
  [∀ i, TopologicalSpace (C i)] [∀ i, IsTopologicalRing (C i)]
  [∀ i, ContinuousSMul ((v i).adicCompletion F) (C i)]

theorem denseRange_finiteAlgebraDiagonal_of_bases (hv : Function.Injective v)
    (f : ∀ i, A →ₐ[F] C i) {m : ℕ} (b : Fin m → A)
    (c : ∀ i, Module.Basis (Fin m) ((v i).adicCompletion F) (C i))
    (hc : ∀ i j, c i j = f i (b j)) : DenseRange (fun a : A => fun i => f i a) := by
  let E : (∀ i, Fin m → (v i).adicCompletion F) → (∀ i, C i) :=
    fun t i => ∑ j, t i j • c i j
  have hcont : Continuous E := by
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j _
    have ht : Continuous (fun t : ∀ i, Fin m → (v i).adicCompletion F => t i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact ht.smul continuous_const
  have hsurj : Function.Surjective E := by
    intro x
    refine ⟨fun i j => (c i).repr (x i) j, ?_⟩
    funext i
    exact (c i).sum_repr (x i)
  have hd := hsurj.denseRange.comp (FiniteScalarDensity.denseRange_finiteAffineDiagonal v hv m) hcont
  apply hd.mono
  rintro x ⟨a, rfl⟩
  refine ⟨∑ j, a j • b j, ?_⟩
  funext i
  change f i (∑ j, a j • b j) = ∑ j, algebraMap F ((v i).adicCompletion F) (a j) • c i j
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, hc, IsScalarTower.algebraMap_smul]

theorem denseRange_finiteAlgebraUnits_of_bases [FiniteDimensional F A]
    [∀ i, IsOpenUnits (C i)] (hv : Function.Injective v)
    (f : ∀ i, A →ₐ[F] C i) (hf : ∀ i, Function.Injective (f i))
    {m : ℕ} (b : Fin m → A)
    (c : ∀ i, Module.Basis (Fin m) ((v i).adicCompletion F) (C i))
    (hc : ∀ i j, c i j = f i (b j)) :
    DenseRange (UnitsWeakApproximation.unitsPiDiagonal (fun i => (f i).toRingHom)) :=
  UnitsWeakApproximation.denseRange_unitsPiDiagonal (F := F) _ hf
    (denseRange_finiteAlgebraDiagonal_of_bases v hv f b c hc)

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteAlgebraApproximation
