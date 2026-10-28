import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.CentralizerEquations

/-! # Adjoint Kernel Field Finite -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointKernelFieldFinite.Construction

noncomputable section

/-! The adjoint kernel is finite over every extension of the base field. -/

open scoped Classical
open _root_.MvPolynomial

theorem finite_geometric_infinitesimalCentralizer_locus
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (hsemi : G.IsSemisimple) :
    (zeroLocus (AlgebraicClosure k) (Infinitesimal.CentralizerEquations.Construction.infinitesimalCentralizerIdeal G)).Finite := by
  let K := AlgebraicClosure k
  let Z := zeroLocus K (Infinitesimal.CentralizerEquations.Construction.infinitesimalCentralizerIdeal G)
  let q : Z → G.GeometricPoints := fun x =>
    (Infinitesimal.CentralizerEquations.Construction.infinitesimalCentralizer_zeroLocus_point G x.property).choose
  have hq (x : Z) : (∀ i j, (q x).val i j = x.val (i, j)) ∧
      ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G,
        ((q x).val : Matrix (Fin n) (Fin n) K) * A.map (algebraMap k K) =
          A.map (algebraMap k K) * ((q x).val : Matrix (Fin n) (Fin n) K) :=
    (Infinitesimal.CentralizerEquations.Construction.infinitesimalCentralizer_zeroLocus_point G x.property).choose_spec
  let S := {g : G.GeometricPoints |
    ∀ A : Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)),
      (g.val : Matrix (Fin n) (Fin n) K) * A.val *
        ((g.val⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) = A.val}
  let : Finite S := (AdjointKernelCenter.Construction.semisimple_geometric_adjoint_kernel_finite G hG hsemi).to_subtype
  let f : Z → S := fun x => ⟨q x, by
    intro A
    have he := Infinitesimal.CentralizerEquations.Construction.commutes_infinitesimal_extension_of_commutes_base G hG
      ((q x).val : Matrix (Fin n) (Fin n) K) (hq x).2 A.property
    rw [he, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    funext ij
    have hv := congrArg (fun z : S => z.val.val ij.1 ij.2) he
    rw [(hq x).1, (hq y).1] at hv
    exact hv
  let : Finite Z := Finite.of_injective f hf
  exact Set.toFinite _

theorem finite_infinitesimalCentralizer_locus
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (hsemi : G.IsSemisimple) :
    (zeroLocus K (Infinitesimal.CentralizerEquations.Construction.infinitesimalCentralizerIdeal G)).Finite :=
  AlgebraicLocusBaseChange.Construction.finite_zeroLocus_of_finite_algClosure (Infinitesimal.CentralizerEquations.Construction.infinitesimalCentralizerIdeal G)
    (finite_geometric_infinitesimalCentralizer_locus G hG hsemi)

theorem semisimple_adjoint_kernel_field_finite
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (hsemi : G.IsSemisimple) :
    Set.Finite {g : G.Points (algebraMap k K) |
      ∀ A : Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)),
        (g.val : Matrix (Fin n) (Fin n) K) * A.val *
          ((g.val⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) = A.val} := by
  let f : G.Points (algebraMap k K) → ((Fin n × Fin n) → K) := fun g ij => g.val ij.1 ij.2
  have hf : Function.Injective f := by
    intro g h he
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact congrFun he (i, j)
  apply Set.Finite.of_finite_image (f := f)
    ((finite_infinitesimalCentralizer_locus (K := K) G hG hsemi).subset ?_) hf.injOn
  rintro _ ⟨g, hg, rfl⟩
  apply Infinitesimal.CentralizerEquations.Construction.point_mem_infinitesimalCentralizer_zeroLocus G g
  intro A hA
  have he := hg ⟨A.map (algebraMap k K), CharZeroTangent.Construction.infinitesimalStabilizer_coefficient_map G hG hA⟩
  have hm := congrArg (fun M : Matrix (Fin n) (Fin n) K =>
    M * (g.val : Matrix (Fin n) (Fin n) K)) he
  simpa only [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one] using hm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointKernelFieldFinite.Construction
