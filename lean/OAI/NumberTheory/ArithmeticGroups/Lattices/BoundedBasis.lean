import OAI.NumberTheory.ArithmeticGroups.Lattices.BasisLift

/-! # Bounded Basis -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedBasis.Construction

noncomputable section

section

/-! One step of lattice basis reduction, with controlled lifts from an
orthogonal projection. -/

open scoped Classical
open Set _root_.Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def latticeProjection (Λ : Submodule ℤ E) (v : E) : Λ →ₗ[ℤ] ProjectedLattice.Construction.projectedLattice Λ v where
  toFun x := ⟨ProjectedLattice.Construction.perpendicularProjection v x.val, ⟨x.val, x.property, rfl⟩⟩
  map_add' x y := Subtype.ext ((ProjectedLattice.Construction.perpendicularProjection v).map_add x.val y.val)
  map_smul' m x := Subtype.ext
    (((ProjectedLattice.Construction.perpendicularProjection v).toLinearMap.restrictScalars ℤ).map_smul m x.val)

@[simp] theorem latticeProjection_coe (Λ : Submodule ℤ E) (v : E) (x : Λ) :
    (latticeProjection Λ v x).val = ProjectedLattice.Construction.perpendicularProjection v x.val := rfl

theorem shortest_projection_kernel (Λ : Submodule ℤ E) (v : Λ) (hv0 : v.val ≠ 0)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖v.val‖ ≤ ‖x‖) :
    (latticeProjection Λ v.val).ker = Submodule.span ℤ ({v} : Set Λ) := by
  ext x
  change latticeProjection Λ v.val x = 0 ↔ _
  rw [← Subtype.val_inj]
  change ProjectedLattice.Construction.perpendicularProjection v.val x.val = 0 ↔ _
  rw [ProjectedLattice.Construction.perpendicularProjection, Submodule.orthogonalProjectionOnto_eq_zero_iff,
    Submodule.orthogonal_orthogonal]
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨m, hm⟩ := ShortestVector.Construction.shortest_vector_scalar_is_integer Λ v.property hv0 hmin t
      (ht ▸ x.property)
    refine Submodule.mem_span_singleton.mpr ⟨m, Subtype.ext ?_⟩
    simpa only [hm, Int.cast_smul_eq_zsmul, Submodule.coe_smul] using ht
  · intro hx
    obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp hx
    refine Submodule.mem_span_singleton.mpr ⟨(m : ℝ), ?_⟩
    simpa only [Int.cast_smul_eq_zsmul, Submodule.coe_smul] using congrArg Subtype.val hm

theorem exists_reduced_basis_lift (Λ : Submodule ℤ E) (v : Λ) (hv0 : v.val ≠ 0)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖v.val‖ ≤ ‖x‖)
    {ι : Type*} (b : Basis ι ℤ (ProjectedLattice.Construction.projectedLattice Λ v.val)) :
    ∃ B : Basis (Unit ⊕ ι) ℤ Λ,
      B (Sum.inl ()) = v ∧
      ∀ i, ProjectedLattice.Construction.perpendicularProjection v.val (B (Sum.inr i)).val = (b i).val ∧
        ‖(B (Sum.inr i)).val‖ ≤ ‖(b i).val‖ + ‖v.val‖ / 2 := by
  have hpre (i : ι) : ∃ y : Λ,
      latticeProjection Λ v.val y = b i ∧ ‖y.val‖ ≤ ‖(b i).val‖ + ‖v.val‖ / 2 := by
    obtain ⟨x, hx, he⟩ := (b i).property
    obtain ⟨y, hy, hyp, hyb⟩ := ProjectedLattice.Construction.projection_reduced_lift Λ v.property hx
    refine ⟨⟨y, hy⟩, Subtype.ext (hyp.trans he), ?_⟩
    simpa only [show ProjectedLattice.Construction.perpendicularProjection v.val x = (b i).val from he] using hyb
  choose u hu hub using hpre
  let : Module.IsTorsionFree ℤ E := Module.IsTorsionFree.trans ℝ
  obtain ⟨B, hB0, hBi⟩ := BasisLift.Construction.basis_lift_cyclic_kernel (latticeProjection Λ v.val) v
    (show v ≠ 0 from fun he => hv0 (congrArg Subtype.val he))
    (shortest_projection_kernel Λ v hv0 hmin) b u hu
  refine ⟨B, hB0, fun i => ?_⟩
  rw [hBi]
  exact ⟨congrArg Subtype.val (hu i), hub i⟩

end

/-! A lattice spanned by short vectors has an integral basis with uniformly
bounded lengths. The proof iterates shortest-vector projection. -/

open scoped Classical
open Set _root_.Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem projection_short_vectors_span (Λ : Submodule ℤ E) (R : ℝ)
    (hspan : Submodule.span ℝ {x : E | x ∈ Λ ∧ ‖x‖ ≤ R} = ⊤) (v : E) :
    Submodule.span ℝ {x : (Submodule.span ℝ ({v} : Set E))ᗮ |
      x ∈ ProjectedLattice.Construction.projectedLattice Λ v ∧ ‖x‖ ≤ R} = ⊤ := by
  let p := (ProjectedLattice.Construction.perpendicularProjection v).toLinearMap
  have hp : p.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro y
    exact ⟨y.val, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self y⟩
  apply top_unique
  calc
    ⊤ = Submodule.span ℝ (p '' {x : E | x ∈ Λ ∧ ‖x‖ ≤ R}) := by
      rw [← Submodule.map_span, hspan, Submodule.map_top, hp]
    _ ≤ Submodule.span ℝ {x | x ∈ ProjectedLattice.Construction.projectedLattice Λ v ∧ ‖x‖ ≤ R} := by
      apply Submodule.span_mono
      rintro _ ⟨x, ⟨hx, hxb⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      exact ((Submodule.span ℝ ({v} : Set E))ᗮ.norm_orthogonalProjectionOnto_apply_le x).trans hxb

theorem bounded_spanning_lattice_basis (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (hdim : finrank ℝ E = n)
    (R : ℝ) (hR : 0 ≤ R)
    (hspan : Submodule.span ℝ {x : E | x ∈ Λ ∧ ‖x‖ ≤ R} = ⊤) :
    ∃ b : Basis (Fin n) ℤ Λ, ∀ i, ‖(b i).val‖ ≤ n * R := by
  induction n generalizing E with
  | zero =>
    let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    exact ⟨Basis.empty Λ, fun i => Fin.elim0 i⟩
  | succ n ih =>
    have hy : ∃ y : E, (y ∈ Λ ∧ ‖y‖ ≤ R) ∧ y ≠ 0 := by
      by_contra! hzero
      have he : (⊤ : Submodule ℝ E) = ⊥ := hspan.symm.trans
        (Submodule.span_eq_bot.mpr (fun x hx => hzero x hx))
      have hz := congrArg (fun W : Submodule ℝ E => finrank ℝ W) he
      simp only [finrank_top, finrank_bot] at hz
      omega
    obtain ⟨y, ⟨hyΛ, hyR⟩, hy0⟩ := hy
    obtain ⟨v, hvΛ, hv0, hmin⟩ := ShortestVector.Construction.exists_shortest_lattice_vector Λ y hyΛ hy0
    have hvR : ‖v‖ ≤ R := (hmin y hyΛ hy0).trans hyR
    let W : Submodule ℝ E := Submodule.span ℝ {v}
    let Λ' := ProjectedLattice.Construction.projectedLattice Λ v
    let : DiscreteTopology Λ' := ProjectedLattice.Construction.projected_lattice_discrete Λ hvΛ hv0 hmin
    have hdim' : finrank ℝ Wᗮ = n := by
      have he := W.finrank_add_finrank_orthogonal
      have hW : finrank ℝ W = 1 := finrank_span_singleton hv0
      omega
    obtain ⟨b, hb⟩ := ih Λ' hdim' (projection_short_vectors_span Λ R hspan v)
    obtain ⟨B, hB0, hBi⟩ := exists_reduced_basis_lift Λ ⟨v, hvΛ⟩ hv0 hmin b
    have hB (i : Unit ⊕ Fin n) : ‖(B i).val‖ ≤ (n + 1 : ℕ) * R := by
      rcases i with u | i
      · cases u
        rw [hB0]
        have hn : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg n) hR
        push_cast
        change ‖v‖ ≤ _
        nlinarith
      · have hh := (hBi i).2
        have hi := hb i
        change ‖(b i).val‖ ≤ (n : ℝ) * R at hi
        push_cast
        nlinarith
    let e : (Unit ⊕ Fin n) ≃ Fin (n + 1) := Fintype.equivFinOfCardEq (by simp [Nat.add_comm])
    refine ⟨B.reindex e, fun i => ?_⟩
    simpa only [Basis.reindex_apply] using hB (e.symm i)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedBasis.Construction
