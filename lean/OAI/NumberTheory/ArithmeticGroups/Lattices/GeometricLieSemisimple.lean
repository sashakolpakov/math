import OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraicLieRadical
import OAI.NumberTheory.ArithmeticGroups.Lattices.BaseChange
import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleLieCharacters

/-! # Geometric Lie Semisimple -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricLieSemisimple.Construction

noncomputable section

/-! Geometric semisimplicity of the original matrix group gives
semisimplicity of its concrete Lie algebra over the algebraic closure.
The proof uses the algebraic hull, without an analytic embedding. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

theorem infinitesimal_radical_eq_bot_of_finite_normal_solvable
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n)
    (hfinite : ∀ N : Subgroup G.RationalPoints, N.Normal → Group.IsSolvable N → Finite N) :
    LieAlgebra.radical k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) = ⊥ := by
  let L := Infinitesimal.Action.Construction.infinitesimalStabilizer G
  let I := LieAlgebra.radical k L
  let S := I.toLieSubalgebra.map L.incl
  let e : I ≃ₗ⁅k⁆ S := I.toLieSubalgebra.equivMapOfInjective (f := L.incl) Subtype.val_injective
  let : LieAlgebra.IsSolvable S := e.surjective.lieAlgebra_isSolvable
  have hS : S ≤ L := by
    rintro _ ⟨A, _, rfl⟩
    exact A.property
  have hconj (g : G.RationalPoints) (A : Matrix (Fin n) (Fin n) k) (hA : A ∈ S) :
      (g.val : Matrix (Fin n) (Fin n) k) * A *
        ((g.val⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) ∈ S := by
    obtain ⟨B, hB, rfl⟩ := hA
    refine ⟨ExponentialNormal.Construction.infinitesimalAdjoint G g B, ExponentialNormal.Construction.LieEquiv_preserves_radical (ExponentialNormal.Construction.infinitesimalAdjoint G g) hB, ?_⟩
    exact ExponentialNormal.Construction.infinitesimalAdjoint_apply G g B
  have hzero : S = ⊥ :=
    AlgebraicLieRadical.Construction.algebraic_solvable_Lie_eq_bot_of_finite_normal_solvable G hfinite S hS hconj
  apply le_antisymm _ bot_le
  intro A hA
  have hm : A.val ∈ S := ⟨A, hA, rfl⟩
  rw [hzero] at hm
  change A = 0
  exact Subtype.ext hm

theorem geometric_infinitesimal_isSemisimple
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsSemisimple) :
    LieAlgebra.IsSemisimple (AlgebraicClosure k)
      (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k)))) := by
  let H := BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))
  have hpoints : H.subgroup (AlgebraicClosure k) (RingHom.id (AlgebraicClosure k)) =
      G.subgroup (AlgebraicClosure k) (algebraMap k (AlgebraicClosure k)) := by
    change G.subgroup (AlgebraicClosure k)
      ((RingHom.id (AlgebraicClosure k)).comp (algebraMap k (AlgebraicClosure k))) = _
    rw [RingHom.id_comp]
  let e : H.RationalPoints ≃* G.GeometricPoints := MulEquiv.subgroupCongr hpoints
  have hfinite : ∀ N : Subgroup H.RationalPoints, N.Normal → Group.IsSolvable N → Finite N := by
    intro N hN hsol
    let : N.Normal := hN
    let : Group.IsSolvable N := hsol
    let M := N.map e.toMonoidHom
    let : M.Normal := Subgroup.Normal.map hN e.toMonoidHom e.surjective
    let : Group.IsSolvable M := Group.isSolvable_of_surjective
      (f := e.toMonoidHom.subgroupMap N) (MonoidHom.subgroupMap_surjective _ _)
    let : Finite M := RationalGeometricEquiv.Construction.semisimple_geometric_normal_solvable_finite G hG M
    apply Finite.of_injective (e.toMonoidHom.subgroupMap N)
    intro x y h
    apply Subtype.ext
    apply e.injective
    exact congrArg (fun z : M => z.val) h
  let : LieAlgebra.HasTrivialRadical (AlgebraicClosure k) (Infinitesimal.Action.Construction.infinitesimalStabilizer H) :=
    ⟨infinitesimal_radical_eq_bot_of_finite_normal_solvable H hfinite⟩
  infer_instance

theorem geometric_infinitesimal_no_abelian_characters
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsSemisimple)
    {A : Type*} [LieRing A] [LieAlgebra (AlgebraicClosure k) A] [IsLieAbelian A]
    (f : Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k)))
      →ₗ⁅AlgebraicClosure k⁆ A) : f = 0 := by
  let : LieAlgebra.IsSemisimple (AlgebraicClosure k)
      (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k)))) :=
    geometric_infinitesimal_isSemisimple G hG
  exact SemisimpleLieCharacters.Construction.semisimpleLie_hom_to_abelian_eq_zero f

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricLieSemisimple.Construction
