import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleLieCharacters

/-! # Perfect Scalar Extension -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PerfectScalarExtension.Construction

noncomputable section

/-! Perfectness of a Lie algebra (being spanned by its commutators)
ascends and descends along field extensions. -/

open scoped TensorProduct

theorem derived_one_baseChange
    {k K L : Type*} [Field k] [Field K] [Algebra k K] [LieRing L] [LieAlgebra k L] :
    (LieAlgebra.derivedSeries k L 1).baseChange K =
      LieAlgebra.derivedSeries K (K ⊗[k] L) 1 := by
  change (⁅(⊤ : LieIdeal k L), (⊤ : LieIdeal k L)⁆).baseChange K =
    ⁅(⊤ : LieIdeal K (K ⊗[k] L)), (⊤ : LieIdeal K (K ⊗[k] L))⁆
  rw [LieSubmodule.lie_baseChange, LieSubmodule.baseChange_top]

theorem perfect_baseChange_iff
    {k K L : Type*} [Field k] [Field K] [Algebra k K] [LieRing L] [LieAlgebra k L] :
    LieAlgebra.derivedSeries K (K ⊗[k] L) 1 = ⊤ ↔ LieAlgebra.derivedSeries k L 1 = ⊤ := by
  rw [← derived_one_baseChange]
  constructor
  · intro h
    apply LieSubmodule.toSubmodule_injective
    apply Submodule.baseChange_injective (A := K)
    have he := congrArg (fun I : LieIdeal K (K ⊗[k] L) => I.toSubmodule) h
    simpa only [LieSubmodule.coe_baseChange, LieSubmodule.top_toSubmodule, Submodule.baseChange_top]
      using he
  · intro h
    rw [h, LieSubmodule.baseChange_top]

theorem perfect_of_LieEquiv
    {k L M : Type*} [CommRing k] [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    (e : L ≃ₗ⁅k⁆ M) (h : LieAlgebra.derivedSeries k L 1 = ⊤) :
    LieAlgebra.derivedSeries k M 1 = ⊤ := by
  rw [← LieIdeal.derivedSeries_map_eq (f := e.toLieHom) 1 e.surjective, h,
    ← e.toLieHom.idealRange_eq_map]
  exact e.toLieHom.idealRange_eq_top_of_surjective e.surjective

theorem perfectLie_hom_to_abelian_eq_zero
    {k L A : Type*} [CommRing k] [LieRing L] [LieAlgebra k L]
    (h : LieAlgebra.derivedSeries k L 1 = ⊤)
    [LieRing A] [LieAlgebra k A] [IsLieAbelian A] (f : L →ₗ⁅k⁆ A) : f = 0 := by
  have hker : (LieAlgebra.derivedSeries k L 1 : Submodule k L) ≤ (f.ker : Submodule k L) := by
    rw [LieAlgebra.coe_derivedSeries_one_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, y, rfl⟩
    change f ⁅x, y⁆ = 0
    rw [f.map_lie]
    exact LieModule.IsTrivial.trivial _ _
  rw [h] at hker
  ext x
  exact hker (Submodule.mem_top : x ∈ (⊤ : Submodule k L))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PerfectScalarExtension.Construction
