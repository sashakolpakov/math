import OAI.AlgebraicGeometry.ComplexMultiplication.CM.ImaginaryElement
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! # Period Space -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CM

noncomputable section

/-!
# The lattice in the selected CM embedding space

Choosing one embedding at every infinite place identifies the usual mixed
embedding space with a complex vector space. The image of the ring of
integers is a discrete full lattice there. Its additive quotient is compact.
This constructs the underlying topological torus; projectivity and the
identification of its geometric cohomology are separate steps.
-/

open scoped Classical _root_.NumberField

open _root_.NumberField

variable (E : Type*) [Field E] [Algebra ℚ E]

/-- One complex coordinate for each conjugate pair of embeddings. -/
abbrev PeriodSpace.CMPeriodSpace := InfinitePlace E → ℂ

variable {E} (ε : TypeHodgeStructure.CMEmbeddingType E)

/-- Adjust the canonical embedding at a place to the embedding selected by the CM type. -/
def TypeHodgeStructure.CMEmbeddingType.periodConjugation (v : InfinitePlace E) : ℂ ≃ₗ[ℝ] ℂ :=
  if ε.val v.embedding.toRatAlgHom then LinearEquiv.refl ℝ ℂ
  else Complex.conjAe.toLinearEquiv

theorem TypeHodgeStructure.CMEmbeddingType.periodConjugation_involutive (v : InfinitePlace E) (z : ℂ) :
    ε.periodConjugation v (ε.periodConjugation v z) = z := by
  by_cases hv : ε.val v.embedding.toRatAlgHom = true
  · simp [TypeHodgeStructure.CMEmbeddingType.periodConjugation, hv]
  · simp [TypeHodgeStructure.CMEmbeddingType.periodConjugation, hv]

theorem TypeHodgeStructure.CMEmbeddingType.periodConjugation_embedding (v : InfinitePlace E) (x : E) :
    ε.periodConjugation v (v.embedding x) = ε.placeEmbedding v x := by
  by_cases hv : ε.val v.embedding.toRatAlgHom = true
  · simp [TypeHodgeStructure.CMEmbeddingType.periodConjugation, TypeHodgeStructure.CMEmbeddingType.placeEmbedding, hv]
  · simp [TypeHodgeStructure.CMEmbeddingType.periodConjugation, TypeHodgeStructure.CMEmbeddingType.placeEmbedding, hv, EmbeddingHodgeType.CM.conjugateEmbedding_apply]

/-- The actual field embedding in the selected complex coordinates. -/
def TypeHodgeStructure.CMEmbeddingType.periodEmbedding : E →+* PeriodSpace.CMPeriodSpace E :=
  RingHom.pi fun v => (ε.placeEmbedding v).toRingHom

@[simp]
theorem TypeHodgeStructure.CMEmbeddingType.periodEmbedding_apply (x : E) (v : InfinitePlace E) :
    ε.periodEmbedding x v = ε.placeEmbedding v x := rfl

/-- All embeddings are the selected embeddings and their conjugates, without repetition. -/
def TypeHodgeStructure.CMEmbeddingType.embeddingPairEquiv : (InfinitePlace E × Bool) ≃ (E →ₐ[ℚ] ℂ) where
  toFun p := if p.2 then ε.placeEmbedding p.1 else EmbeddingHodgeType.CM.conjugateEmbedding (ε.placeEmbedding p.1)
  invFun σ := (InfinitePlace.mk σ.toRingHom, ε.val σ)
  left_inv p := by
    rcases p with ⟨v, b⟩
    cases b
    · apply Prod.ext
      · change InfinitePlace.mk (ComplexEmbedding.conjugate (ε.placeEmbedding v).toRingHom) = v
        rw [InfinitePlace.mk_conjugate_eq, ε.mk_placeEmbedding]
      · simp [ε.property, ε.placeEmbedding_positive]
    · apply Prod.ext
      · exact ε.mk_placeEmbedding v
      · exact ε.placeEmbedding_positive v
  right_inv σ := by
    by_cases hσ : ε.val σ = true
    · simpa only [hσ, ↓reduceIte] using ε.placeEmbedding_mk σ hσ
    · have hc : ε.val (EmbeddingHodgeType.CM.conjugateEmbedding σ) = true := by
        rw [ε.property, Bool.eq_false_iff.mpr hσ, Bool.not_false]
      have hp := ε.placeEmbedding_mk (EmbeddingHodgeType.CM.conjugateEmbedding σ) hc
      have hm : InfinitePlace.mk (EmbeddingHodgeType.CM.conjugateEmbedding σ).toRingHom =
          InfinitePlace.mk σ.toRingHom := InfinitePlace.mk_conjugate_eq σ.toRingHom
      rw [hm] at hp
      simp only [Bool.eq_false_iff.mpr hσ, Bool.false_eq_true, ↓reduceIte, hp,
        EmbeddingHodgeType.CM.conjugateEmbedding_involutive]

variable [NumberField E] [IsCMField E]

omit [IsCMField E] in
/-- A sum over embeddings groups into the two embeddings at each infinite place. -/
theorem TypeHodgeStructure.CMEmbeddingType.sum_embeddings_eq_sum_places (f : (E →ₐ[ℚ] ℂ) → ℂ) :
    ∑ σ, f σ = ∑ v : InfinitePlace E,
      (f (ε.placeEmbedding v) + f (EmbeddingHodgeType.CM.conjugateEmbedding (ε.placeEmbedding v))) := by
  rw [← Equiv.sum_comp ε.embeddingPairEquiv f, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, TypeHodgeStructure.CMEmbeddingType.embeddingPairEquiv, Equiv.coe_fn_mk, Bool.false_eq_true, ↓reduceIte]

/-- Transport from the mixed embedding space, using total complexity to eliminate real places. -/
def TypeHodgeStructure.CMEmbeddingType.mixedPeriodEquiv : mixedEmbedding.mixedSpace E ≃ₗ[ℝ] PeriodSpace.CMPeriodSpace E where
  toFun x v := ε.periodConjugation v (x.2 ⟨v, IsTotallyComplex.isComplex v⟩)
  invFun y := (fun _ => 0, fun w => ε.periodConjugation w.val (y w.val))
  left_inv x := by
    apply Prod.ext
    · funext w
      exact ((InfinitePlace.not_isReal_iff_isComplex.mpr
        (IsTotallyComplex.isComplex w.val)) w.property).elim
    · funext w
      exact ε.periodConjugation_involutive w.val (x.2 w)
  right_inv y := by
    funext v
    exact ε.periodConjugation_involutive v (y v)
  map_add' x y := by
    funext v
    exact map_add (ε.periodConjugation v) _ _
  map_smul' r x := by
    funext v
    exact map_smul (ε.periodConjugation v) r _

theorem TypeHodgeStructure.CMEmbeddingType.mixedPeriodEquiv_mixedEmbedding (x : E) :
    ε.mixedPeriodEquiv (mixedEmbedding E x) = ε.periodEmbedding x := by
  funext v
  exact ε.periodConjugation_embedding v x

/-- The real-linear equivalence is continuous in the usual finite-dimensional topologies. -/
def TypeHodgeStructure.CMEmbeddingType.mixedPeriodContinuousEquiv : mixedEmbedding.mixedSpace E ≃L[ℝ] PeriodSpace.CMPeriodSpace E :=
  ε.mixedPeriodEquiv.toContinuousLinearEquiv

/-- The lattice transported to the selected embedding space. -/
def TypeHodgeStructure.CMEmbeddingType.periodIntegerLattice : Submodule ℤ (PeriodSpace.CMPeriodSpace E) :=
  ZLattice.comap ℝ (mixedEmbedding.integerLattice E)
    ε.mixedPeriodContinuousEquiv.symm.toLinearMap

instance TypeHodgeStructure.CMEmbeddingType.periodIntegerLattice_discrete : DiscreteTopology ε.periodIntegerLattice := by
  unfold TypeHodgeStructure.CMEmbeddingType.periodIntegerLattice
  infer_instance

instance TypeHodgeStructure.CMEmbeddingType.periodIntegerLattice_isZLattice : IsZLattice ℝ ε.periodIntegerLattice := by
  unfold TypeHodgeStructure.CMEmbeddingType.periodIntegerLattice
  infer_instance

/-- The transported lattice is precisely the image of the actual ring of integers. -/
theorem TypeHodgeStructure.CMEmbeddingType.mem_periodIntegerLattice (z : PeriodSpace.CMPeriodSpace E) :
    z ∈ ε.periodIntegerLattice ↔ ∃ a : 𝓞 E, ε.periodEmbedding (a : E) = z := by
  change (∃ a : 𝓞 E, mixedEmbedding E (a : E) = ε.mixedPeriodEquiv.symm z) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← ε.mixedPeriodEquiv_mixedEmbedding, ha, LinearEquiv.apply_symm_apply]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply ε.mixedPeriodEquiv.injective
    rw [ε.mixedPeriodEquiv_mixedEmbedding, ha, LinearEquiv.apply_symm_apply]

/-- The additive quotient by the full CM integer lattice. -/
abbrev TypeHodgeStructure.CMEmbeddingType.periodTorus := PeriodSpace.CMPeriodSpace E ⧸ ε.periodIntegerLattice.toAddSubgroup

/-- A fundamental parallelepiped maps onto the quotient, so the CM torus is compact. -/
instance TypeHodgeStructure.CMEmbeddingType.periodTorus_compact : CompactSpace ε.periodTorus := by
  apply isCompact_univ_iff.mp
  have hc := IsZLattice.isCompact_range_of_periodic ε.periodIntegerLattice
    (QuotientAddGroup.mk : PeriodSpace.CMPeriodSpace E → ε.periodTorus)
    QuotientAddGroup.continuous_mk (by
      intro z w hw
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
  rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at hc

instance TypeHodgeStructure.CMEmbeddingType.periodTorus_t2 : T2Space ε.periodTorus := by
  let : DiscreteTopology ε.periodIntegerLattice.toAddSubgroup :=
    ε.periodIntegerLattice_discrete
  let : IsClosed (ε.periodIntegerLattice.toAddSubgroup : Set (PeriodSpace.CMPeriodSpace E)) :=
    AddSubgroup.isClosed_of_discreteTopology
  infer_instance

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CM
