import OAI.NumberTheory.ArithmeticGroups.Lattices.UniformLieLinearSystem
import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.MixedLattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.QuadraticInvariant

/-! # Lie Eq -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieEq.Construction

noncomputable section

section

/-! Membership in the Minkowski Lie space is equivalent to Lie-algebra
membership at every archimedean completion. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

attribute [local instance] LieRing.ofAssociativeRing

@[instance_reducible] def mixedSpaceBaseAlgebra (k : Type) [Field k] : Algebra k (mixedSpace k) :=
  (mixedEmbedding k).toAlgebra

attribute [local instance] mixedSpaceBaseAlgebra

def mixedCompletionAlgEvaluation {k : Type} [Field k] (v : InfinitePlace k) :
    mixedSpace k →ₐ[k] v.Completion where
  toRingHom := QuadraticInvariant.Construction.mixedCompletionEvaluation v
  commutes' := QuadraticInvariant.Construction.mixedCompletionEvaluation_embedding v

theorem mixedCompletionEvaluation_jointly_injective
    {k : Type} [Field k] (x y : mixedSpace k)
    (h : ∀ v : InfinitePlace k, QuadraticInvariant.Construction.mixedCompletionEvaluation v x = QuadraticInvariant.Construction.mixedCompletionEvaluation v y) : x = y := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace k).symm.injective
  funext v
  exact h v

theorem lieMixedModule_eq_extended_kernel
    {k ι : Type} [Field k] [NumberField k] [Fintype ι] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (f : Matrix (Fin n) (Fin n) k →ₗ[k] (ι → k))
    (hf : f.ker = (Infinitesimal.Action.Construction.infinitesimalStabilizer G).toSubmodule) :
    Lie.MixedLattice.Construction.lieMixedModule G = (MatrixFlatExtension.Construction.matrixLinearSystemExtension (R := mixedSpace k) f).ker := by
  rw [← MatrixFlatExtension.Construction.matrixLinearSystemExtension_kernel, hf,
    MatrixFlatExtension.Construction.matrixSubmoduleAlgebraExtension_eq_span, Lie.MixedLattice.Construction.lieMixedModule_eq_matrix_span]
  rfl

theorem lieMixedModule_mem_iff_completions
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A : Matrix (Fin n) (Fin n) (mixedSpace k)) :
    A ∈ Lie.MixedLattice.Construction.lieMixedModule G ↔
      ∀ v : InfinitePlace k, A.map (QuadraticInvariant.Construction.mixedCompletionEvaluation v) ∈
        Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k v.Completion)) := by
  obtain ⟨ι, hι, f, hf, hfields⟩ := UniformLieLinearSystem.Construction.exists_uniform_infinitesimal_linear_system G hG
  let : Fintype ι := hι
  rw [lieMixedModule_eq_extended_kernel G f hf]
  constructor
  · intro hA v
    change A.map (QuadraticInvariant.Construction.mixedCompletionEvaluation v) ∈
      (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k v.Completion))).toSubmodule
    rw [← hfields v.Completion]
    have h := MatrixFlatExtension.Construction.matrixLinearSystemExtension_coefficient_map f (mixedCompletionAlgEvaluation v) A
    change MatrixFlatExtension.Construction.matrixLinearSystemExtension f (A.map (QuadraticInvariant.Construction.mixedCompletionEvaluation v)) =
      (fun i => QuadraticInvariant.Construction.mixedCompletionEvaluation v (MatrixFlatExtension.Construction.matrixLinearSystemExtension f A i)) at h
    change MatrixFlatExtension.Construction.matrixLinearSystemExtension f (A.map (QuadraticInvariant.Construction.mixedCompletionEvaluation v)) = 0
    rw [h, (show MatrixFlatExtension.Construction.matrixLinearSystemExtension (R := mixedSpace k) f A = 0 from hA)]
    funext i
    exact map_zero _
  · intro hA
    change MatrixFlatExtension.Construction.matrixLinearSystemExtension (R := mixedSpace k) f A = 0
    funext i
    apply mixedCompletionEvaluation_jointly_injective
    intro v
    have hv : A.map (QuadraticInvariant.Construction.mixedCompletionEvaluation v) ∈
        (MatrixFlatExtension.Construction.matrixLinearSystemExtension (R := v.Completion) f).ker := by
      rw [hfields v.Completion]
      exact hA v
    have he := MatrixFlatExtension.Construction.matrixLinearSystemExtension_coefficient_map f (mixedCompletionAlgEvaluation v) A
    have hei := congrFun he i
    change MatrixFlatExtension.Construction.matrixLinearSystemExtension (R := v.Completion) f (A.map (QuadraticInvariant.Construction.mixedCompletionEvaluation v)) i =
      QuadraticInvariant.Construction.mixedCompletionEvaluation v (MatrixFlatExtension.Construction.matrixLinearSystemExtension (R := mixedSpace k) f A i) at hei
    rw [show MatrixFlatExtension.Construction.matrixLinearSystemExtension (R := v.Completion) f
      (A.map (QuadraticInvariant.Construction.mixedCompletionEvaluation v)) = 0 from hv] at hei
    simpa only [Pi.zero_apply, map_zero] using hei.symm

end

section

/-! The Minkowski Lie space maps into the correct Lie algebra under
every coefficient homomorphism to an extension field. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

attribute [local instance] LieRing.ofAssociativeRing mixedSpaceBaseAlgebra

theorem lieMixedModule_mem_field_image
    {k K : Type} [Field k] [NumberField k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (ι : k →+* K) (φ : mixedSpace k →+* K)
    (hφ : ∀ a : k, φ (mixedEmbedding k a) = ι a)
    (A : Matrix (Fin n) (Fin n) (mixedSpace k)) (hA : A ∈ Lie.MixedLattice.Construction.lieMixedModule G) :
    A.map φ ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G ι) := by
  let : Algebra k K := ι.toAlgebra
  let φa : mixedSpace k →ₐ[k] K := { toRingHom := φ, commutes' := hφ }
  obtain ⟨I, hI, f, hf, hfields⟩ := UniformLieLinearSystem.Construction.exists_uniform_infinitesimal_linear_system G hG
  let : Fintype I := hI
  have hker : MatrixFlatExtension.Construction.matrixLinearSystemExtension (R := mixedSpace k) f A = 0 := by
    rw [lieMixedModule_eq_extended_kernel G f hf] at hA
    exact hA
  change A.map φ ∈
    (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))).toSubmodule
  rw [← hfields K]
  have he := MatrixFlatExtension.Construction.matrixLinearSystemExtension_coefficient_map f φa A
  change MatrixFlatExtension.Construction.matrixLinearSystemExtension (R := K) f (A.map φa) = 0
  rw [he, hker]
  ext i
  exact map_zero φa

end

/-! Continuous complex realizations of the Minkowski coefficient
algebra, one for each archimedean place. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

def mixedComplexEvaluation {k : Type} [Field k] (v : InfinitePlace k) :
    mixedSpace k →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding v).comp (QuadraticInvariant.Construction.mixedCompletionEvaluation v)

theorem mixedComplexEvaluation_real
    {k : Type} [Field k] (v : InfinitePlace k) (hv : v.IsReal) (x : mixedSpace k) :
    mixedComplexEvaluation v x = (x.1 ⟨v, hv⟩ : ℂ) := by
  have he := congrArg (fun z : mixedSpace k => z.1 ⟨v, hv⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace k).apply_symm_apply x)
  change InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
    (QuadraticInvariant.Construction.mixedCompletionEvaluation v x) = x.1 ⟨v, hv⟩ at he
  rw [← he, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  rfl

theorem mixedComplexEvaluation_complex
    {k : Type} [Field k] (v : InfinitePlace k) (hv : v.IsComplex) (x : mixedSpace k) :
    mixedComplexEvaluation v x = x.2 ⟨v, hv⟩ := by
  have he := congrArg (fun z : mixedSpace k => z.2 ⟨v, hv⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace k).apply_symm_apply x)
  exact he

theorem continuous_mixedComplexEvaluation
    {k : Type} [Field k] (v : InfinitePlace k) : Continuous (mixedComplexEvaluation v) := by
  by_cases hv : v.IsReal
  · have he : (mixedComplexEvaluation v : mixedSpace k → ℂ) =
        fun x => (x.1 ⟨v, hv⟩ : ℂ) := funext (mixedComplexEvaluation_real v hv)
    rw [he]
    exact Complex.continuous_ofReal.comp
      ((continuous_apply (⟨v, hv⟩ : {w : InfinitePlace k // w.IsReal})).comp continuous_fst)
  · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have he : (mixedComplexEvaluation v : mixedSpace k → ℂ) =
        fun x => x.2 ⟨v, hc⟩ := funext (mixedComplexEvaluation_complex v hc)
    rw [he]
    exact (continuous_apply (⟨v, hc⟩ : {w : InfinitePlace k // w.IsComplex})).comp continuous_snd

theorem continuous_mixedCompletionEvaluation
    {k : Type} [Field k] (v : InfinitePlace k) : Continuous (QuadraticInvariant.Construction.mixedCompletionEvaluation v) := by
  exact (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff.mpr
    (continuous_mixedComplexEvaluation v)

theorem mixedComplexEvaluation_embedding
    {k : Type} [Field k] (v : InfinitePlace k) (a : k) :
    mixedComplexEvaluation v (mixedEmbedding k a) =
      InfinitePlace.Completion.extensionEmbedding v (algebraMap k v.Completion a) := by
  change InfinitePlace.Completion.extensionEmbedding v
      (QuadraticInvariant.Construction.mixedCompletionEvaluation v (mixedEmbedding k a)) = _
  rw [QuadraticInvariant.Construction.mixedCompletionEvaluation_embedding]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieEq.Construction
