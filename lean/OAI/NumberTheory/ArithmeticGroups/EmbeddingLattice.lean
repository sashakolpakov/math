import OAI.NumberTheory.ArithmeticGroups.Coordinates
import OAI.NumberTheory.ArithmeticGroups.Lattice

/-! # Embedding Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel

noncomputable section

section

open scoped Classical _root_.NumberField

open _root_.NumberField

section ProductLattice
variable {ι W : Type*} [Fintype ι] [NormedAddCommGroup W] [NormedSpace ℝ W]
  (L : Submodule ℤ W) [DiscreteTopology L]

def productLattice : Submodule ℤ (ι → W) := Submodule.pi Set.univ (fun _ => L)

instance productLattice_discrete : DiscreteTopology (productLattice (ι := ι) L) := by
  let f : productLattice (ι := ι) L → (ι → L) :=
    fun x i => ⟨x.val i, x.property i (Set.mem_univ i)⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    funext i
    exact congrArg (fun z : ι → L => (z i).val) h

instance productLattice_isZLattice [IsZLattice ℝ L] :
    IsZLattice ℝ (productLattice (ι := ι) L) where
  span_top := by
    apply top_unique
    intro x _
    have hsingle (i : ι) (w : W) : Pi.single i w ∈
        Submodule.span ℝ (productLattice (ι := ι) L : Set (ι → W)) := by
      have hw : w ∈ Submodule.span ℝ (L : Set W) := by rw [IsZLattice.span_top]; trivial
      induction hw using Submodule.span_induction with
      | mem w hw =>
        apply Submodule.subset_span
        intro j _
        by_cases h : j = i
        · subst j; simpa using hw
        · rw [Pi.single_eq_of_ne h]
          exact L.zero_mem
      | zero => simp
      | add u v _ _ hu hv => simpa only [Pi.single_add] using Submodule.add_mem _ hu hv
      | smul a w _ hw => simpa only [Pi.single_smul] using Submodule.smul_mem _ a hw
    have hx : x = ∑ i : ι, Pi.single i (x i) := by ext j; simp
    rw [hx]
    exact Submodule.sum_mem _ (fun i _ => hsingle i (x i))
end ProductLattice

variable {E Place : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Fintype Place]
  (σ : Place → E →ₐ[ℚ] ℂ)
  (hσ : Function.Bijective
    (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))

include hσ

def representativePairs : (Place × Bool) ≃ (E →ₐ[ℚ] ℂ) := Equiv.ofBijective _ hσ

omit [NumberField E] [NumberField.IsCMField E] [Fintype Place] in
lemma representativePairs_conjugate (p : Place × Bool) :
    representativePairs σ hσ (p.1, !p.2) =
      AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (representativePairs σ hσ p) := by
  rcases p with ⟨τ, b⟩
  cases b <;> simp [representativePairs, AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]

def referenceCMType : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E :=
  ⟨fun ρ => Bool.not ((representativePairs σ hσ).symm ρ).2, by
    intro ρ
    obtain ⟨p, rfl⟩ := (representativePairs σ hσ).surjective ρ
    rw [← representativePairs_conjugate]
    simp only [Equiv.symm_apply_apply]⟩

omit [NumberField E] [NumberField.IsCMField E] [Fintype Place] in
lemma referenceCMType_positive (τ : Place) :
    (referenceCMType σ hσ).val (σ τ) = true := by
  have h : representativePairs σ hσ (τ, false) = σ τ := rfl
  change Bool.not ((representativePairs σ hσ).symm (σ τ)).2 = true
  rw [← h, Equiv.symm_apply_apply]
  rfl

omit [NumberField E] [NumberField.IsCMField E] [Fintype Place] in
lemma representatives_injective : Function.Injective σ := by
  intro τ υ h
  have he : representativePairs σ hσ (τ, false) = representativePairs σ hσ (υ, false) := h
  exact congrArg Prod.fst ((representativePairs σ hσ).injective he)

omit [NumberField E] [NumberField.IsCMField E] [Fintype Place] in
lemma representative_place_bijective :
    Function.Bijective (fun τ => InfinitePlace.mk (σ τ).toRingHom) := by
  constructor
  · intro τ υ h
    dsimp only at h
    apply representatives_injective σ hσ
    have hpτ := (referenceCMType σ hσ).placeEmbedding_mk (σ τ)
      (referenceCMType_positive σ hσ τ)
    have hpυ := (referenceCMType σ hσ).placeEmbedding_mk (σ υ)
      (referenceCMType_positive σ hσ υ)
    rw [← hpτ, ← hpυ, h]
  · intro v
    obtain ⟨⟨τ, b⟩, hτ⟩ := hσ.2 v.embedding.toRatAlgHom
    refine ⟨τ, ?_⟩
    change InfinitePlace.mk (σ τ).toRingHom = v
    cases b
    · change σ τ = v.embedding.toRatAlgHom at hτ
      rw [hτ]
      exact InfinitePlace.mk_embedding v
    · change AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ τ) = v.embedding.toRatAlgHom at hτ
      have h := congrArg (fun ρ : E →ₐ[ℚ] ℂ => InfinitePlace.mk ρ.toRingHom) hτ
      change InfinitePlace.mk (ComplexEmbedding.conjugate (σ τ).toRingHom) =
        InfinitePlace.mk v.embedding at h
      simpa only [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding] using h

def representativePlaces : Place ≃ InfinitePlace E :=
  Equiv.ofBijective _ (representative_place_bijective σ hσ)

omit [NumberField E] [NumberField.IsCMField E] [Fintype Place] in
lemma placeEmbedding_representative (τ : Place) :
    (referenceCMType σ hσ).placeEmbedding (representativePlaces σ hσ τ) = σ τ :=
  (referenceCMType σ hσ).placeEmbedding_mk (σ τ) (referenceCMType_positive σ hσ τ)

/-- Reindex the three copies of the CM embedding space by the manuscript's places. -/
def periodCoordinateEquiv : (Fin 3 → AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) ≃ₗ[ℂ] (Place → Geometry.ComplexBall.PrescribedSignsB.Vec) where
  toFun x τ j := x j (representativePlaces σ hσ τ)
  invFun x j v := x ((representativePlaces σ hσ).symm v) j
  left_inv x := by ext j v; simp
  right_inv x := by ext τ j; simp
  map_add' x y := by ext τ j; rfl
  map_smul' a x := by ext τ j; rfl

omit [NumberField E] [NumberField.IsCMField E] [Fintype Place] in
lemma periodCoordinateEquiv_embedding (x : Data.CongruenceLevel.VE E) :
    periodCoordinateEquiv σ hσ
      (fun j => (referenceCMType σ hσ).periodEmbedding (x j)) =
        (fun τ j => σ τ (x j)) := by
  ext τ j
  change (referenceCMType σ hσ).placeEmbedding (representativePlaces σ hσ τ) (x j) = _
  rw [placeEmbedding_representative]

def coordinateLattice : Submodule ℤ (Place → Geometry.ComplexBall.PrescribedSignsB.Vec) :=
  ZLattice.comap ℝ
    (productLattice (ι := Fin 3) (referenceCMType σ hσ).periodIntegerLattice)
    ((periodCoordinateEquiv σ hσ).restrictScalars ℝ).symm.toContinuousLinearEquiv.toLinearMap

instance coordinateLattice_discrete : DiscreteTopology (coordinateLattice σ hσ) := by
  unfold coordinateLattice
  infer_instance

instance coordinateLattice_isZLattice : IsZLattice ℝ (coordinateLattice σ hσ) := by
  unfold coordinateLattice
  infer_instance

lemma mem_coordinateLattice (u : Place → Geometry.ComplexBall.PrescribedSignsB.Vec) :
    u ∈ coordinateLattice σ hσ ↔
      ∃ x : Data.CongruenceLevel.VE E, x ∈ Lattice.CongruenceLevel.standardLattice (E := E) ∧
        (fun τ j => σ τ (x j)) = u := by
  change (∀ j : Fin 3, j ∈ Set.univ →
    ((periodCoordinateEquiv σ hσ).symm u) j ∈
      (referenceCMType σ hσ).periodIntegerLattice) ↔ _
  simp only [Set.mem_univ, forall_true_left]
  constructor
  · intro hu
    have h : ∀ j : Fin 3, ∃ a : NumberField.RingOfIntegers E,
        (referenceCMType σ hσ).periodEmbedding (a : E) =
          ((periodCoordinateEquiv σ hσ).symm u) j := by
      intro j
      exact ((referenceCMType σ hσ).mem_periodIntegerLattice _).mp (hu j)
    choose a ha using h
    refine ⟨fun j => (a j : E), ?_, ?_⟩
    · exact (Lattice.CongruenceLevel.mem_standardLattice _).mpr (fun j => (a j).property)
    · rw [← periodCoordinateEquiv_embedding σ hσ]
      apply (periodCoordinateEquiv σ hσ).eq_symm_apply.mp
      funext j
      exact ha j
  · rintro ⟨x, hx, rfl⟩ j
    rw [← periodCoordinateEquiv_embedding σ hσ, LinearEquiv.symm_apply_apply]
    apply ((referenceCMType σ hσ).mem_periodIntegerLattice _).mpr
    exact ⟨⟨x j, (Lattice.CongruenceLevel.mem_standardLattice x).mp hx j⟩, rfl⟩

end

open scoped Classical

variable {E Place : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Fintype Place]
  (σ : Place → E →ₐ[ℚ] ℂ)
  (hσ : Function.Bijective
    (fun p : Place × Bool =>
      if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))

omit [NumberField E] [NumberField.IsCMField E] [Fintype Place] in
lemma embeddingCoordinates_real (x : Data.CongruenceLevel.VE E) :
    Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x = Coordinates.CongruenceLevel.realCoordinates Place (fun τ j => σ τ (x j)) := by
  ext τ j <;> rfl

omit [NumberField E] [NumberField.IsCMField E] [Fintype Place] in
lemma embeddingCoordinates_injective (μ : Place) : Function.Injective (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ) := by
  intro x y h
  funext j
  apply (σ μ).injective
  exact congrArg (fun z : Geometry.ComplexBall.PrescribedSignsB.Ambient Place => (z μ).1 j) h

include hσ in
theorem period_projection_lattice
    (μ : Place)
    (Ψ : LinearMap.BilinForm ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place))
    (P : Submodule ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place))
    (hP : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * Fintype.card Place)
      (fun x y => Ψ x y) (Coordinates.CongruenceLevel.ambientConjugation Place) P)
    (π : Geometry.ComplexBall.PrescribedSignsB.Ambient Place →ₗ[ℂ] (Fin (3 * Fintype.card Place) → ℂ))
    (hπ : π.ker = P) :
    Function.Injective (fun x : Data.CongruenceLevel.VE E => π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x)) ∧
    ∃ Γ : AddSubgroup (Fin (3 * Fintype.card Place) → ℂ),
      (∀ t, t ∈ Γ ↔ ∃ x : Data.CongruenceLevel.VE E, x ∈ Lattice.CongruenceLevel.standardLattice (E := E) ∧
        t = π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x)) ∧
      DiscreteTopology Γ ∧ CompactSpace ((Fin (3 * Fintype.card Place) → ℂ) ⧸ Γ) := by
  let T := Fin (3 * Fintype.card Place) → ℂ
  let f : (Place → Geometry.ComplexBall.PrescribedSignsB.Vec) →ₗ[ℝ] T := (π.restrictScalars ℝ).comp (Coordinates.CongruenceLevel.realCoordinates Place)
  have hfinj : Function.Injective f :=
    Coordinates.CongruenceLevel.realCoordinates_projection_injective _ Ψ P hP π hπ
  have hd : Module.finrank ℝ (Place → Geometry.ComplexBall.PrescribedSignsB.Vec) = Module.finrank ℝ T := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (Place → Geometry.ComplexBall.PrescribedSignsB.Vec),
      ← Module.finrank_mul_finrank ℝ ℂ T]
    congr 1
    simp [T, Geometry.ComplexBall.PrescribedSignsB.Vec, Module.finrank_pi_fintype, Nat.mul_comm]
  let e : (Place → Geometry.ComplexBall.PrescribedSignsB.Vec) ≃ₗ[ℝ] T := LinearEquiv.ofBijective f
    ⟨hfinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hfinj⟩
  have he (x : Data.CongruenceLevel.VE E) : e (fun τ j => σ τ (x j)) = π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x) := by
    change π (Coordinates.CongruenceLevel.realCoordinates Place (fun τ j => σ τ (x j))) = _
    rw [← embeddingCoordinates_real]
  refine ⟨?_, ?_⟩
  · intro x y h
    have hxy : (fun τ j => σ τ (x j)) = (fun τ j => σ τ (y j)) := by
      apply e.injective
      rwa [he, he]
    apply embeddingCoordinates_injective σ μ
    rw [embeddingCoordinates_real, embeddingCoordinates_real, hxy]
  · let L := ZLattice.comap ℝ (coordinateLattice σ hσ) e.symm.toContinuousLinearEquiv.toLinearMap
    let Γ : AddSubgroup T := L.toAddSubgroup
    have hmem (t : T) : t ∈ Γ ↔ ∃ x : Data.CongruenceLevel.VE E, x ∈ Lattice.CongruenceLevel.standardLattice (E := E) ∧
        t = π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x) := by
      change e.symm t ∈ coordinateLattice σ hσ ↔ _
      rw [mem_coordinateLattice σ hσ]
      apply exists_congr
      intro x
      apply and_congr_right
      intro _
      rw [e.eq_symm_apply, he]
      exact eq_comm
    have hdisc : DiscreteTopology Γ := by
      change DiscreteTopology L
      dsimp only [L]
      infer_instance
    have hcomp : CompactSpace (T ⧸ Γ) := by
      apply isCompact_univ_iff.mp
      have hc := IsZLattice.isCompact_range_of_periodic L
        (QuotientAddGroup.mk : T → T ⧸ Γ) QuotientAddGroup.continuous_mk (by
          intro z w hw
          rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
      rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at hc
    exact ⟨Γ, hmem, hdisc, hcomp⟩

end

end OAI.NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel
