import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixFlatExtension
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.TangentExtension

/-! # Uniform Lie Linear System -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UniformLieLinearSystem.Construction

noncomputable section

/-! One finite matrix linear system describes the Lie algebra over all
extension fields, in a form that also extends to coefficient algebras. -/

open scoped Classical TensorProduct

attribute [local instance] LieRing.ofAssociativeRing

theorem matrixLinearSystemExtension_tangentSystem
    {k K ι : Type} [Field k] [Field K] [Algebra k K] [Fintype ι] {n : ℕ}
    (p : ι → Algebraic.CoordinatePolynomial n k) :
    MatrixFlatExtension.Construction.matrixLinearSystemExtension (R := K) (Finite.TangentEquations.Construction.tangentSystem p) =
      Finite.TangentEquations.Construction.tangentSystem (fun i => MvPolynomial.map (algebraMap k K) (p i)) := by
  apply LinearMap.ext
  intro A
  let x := (MatrixFlatExtension.Construction.matrixAlgebraExtension (k := k) (R := K) n).symm A
  have h := Infinitesimal.TangentExtension.Construction.tangentSystem_baseChange p x
  change TensorProduct.piScalarRight k K K ι ((Finite.TangentEquations.Construction.tangentSystem p).baseChange K x) =
    Finite.TangentEquations.Construction.tangentSystem (fun i => MvPolynomial.map (algebraMap k K) (p i))
      (MatrixFlatExtension.Construction.matrixAlgebraExtension n x) at h
  rw [show MatrixFlatExtension.Construction.matrixAlgebraExtension n x = A from (MatrixFlatExtension.Construction.matrixAlgebraExtension n).apply_symm_apply A] at h
  exact h

theorem exists_uniform_infinitesimal_linear_system
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    ∃ (ι : Type) (_ : Fintype ι) (f : Matrix (Fin n) (Fin n) k →ₗ[k] (ι → k)),
      f.ker = (Infinitesimal.Action.Construction.infinitesimalStabilizer G).toSubmodule ∧
      ∀ (K : Type) [Field K] [Algebra k K],
        (MatrixFlatExtension.Construction.matrixLinearSystemExtension (R := K) f).ker =
          (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))).toSubmodule := by
  obtain ⟨ι, hι, p, hp⟩ := Finite.TangentEquations.Construction.exists_uniform_finite_tangent_system G hG
  let : Fintype ι := hι
  refine ⟨ι, hι, Finite.TangentEquations.Construction.tangentSystem p, ?_, fun K _ _ => ?_⟩
  · have h := hp k
    rw [Infinitesimal.TangentExtension.Construction.matrixGroupBaseChange_self] at h
    simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using h.symm
  · rw [matrixLinearSystemExtension_tangentSystem]
    exact (hp K).symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UniformLieLinearSystem.Construction
