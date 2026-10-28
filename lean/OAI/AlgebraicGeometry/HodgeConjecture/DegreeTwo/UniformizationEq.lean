import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Connected.Clopen
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Uniformization Eq -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.UniformizationEq.Constructions.Uniformization

noncomputable section

/-!
# DegreeTwo: recovering the lattice from a local group uniformization

The results here prove the topological and lattice steps used after constructing
the exponential map. Existence and complex differentiability of that map are
not assumed for an abelian variety and are not claimed by this file.
-/

open _root_.Topology

section Groups

variable {V G : Type*} [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [AddCommGroup G] [TopologicalSpace G]
  [IsTopologicalAddGroup G]

omit [IsTopologicalAddGroup V] in
/-- The image of a local homeomorphic group homomorphism is open and closed;
connectedness of the target therefore proves surjectivity. -/
theorem surjective_of_localHomeomorph [ConnectedSpace G]
    (p : V →+ G) (hp : IsLocalHomeomorph p) : Function.Surjective p := by
  have hopen : IsOpen (p.range : Set G) := by
    simpa only [AddMonoidHom.coe_range, Set.image_univ] using hp.isOpenMap Set.univ isOpen_univ
  let U : OpenAddSubgroup G := ⟨p.range, hopen⟩
  have hall : (U : Set G) = Set.univ :=
    U.isClopen.eq_univ ⟨0, p.range.zero_mem⟩
  intro x
  have hx : x ∈ (U : Set G) := hall.symm ▸ Set.mem_univ x
  exact hx

omit [IsTopologicalAddGroup V] [IsTopologicalAddGroup G] in
/-- Local injectivity makes the kernel discrete. -/
theorem kernel_discrete (p : V →+ G) (hp : IsLocalHomeomorph p) :
    DiscreteTopology p.ker := by
  have himage : p '' (p.ker : Set V) = {0} := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · rintro rfl
      exact ⟨0, p.map_zero, p.map_zero⟩
  have hd : DiscreteTopology (p '' (p.ker : Set V)) := by
    rw [himage]
    infer_instance
  exact hp.isLocalHomeomorphOn.discreteTopology_of_image

/-- The first isomorphism theorem is a homeomorphism for a local
homeomorphic surjection; continuity of its inverse is proved from openness. -/
def quotientHomeomorph (p : V →+ G) (hp : IsLocalHomeomorph p)
    (hs : Function.Surjective p) : (V ⧸ p.ker) ≃ₜ G := by
  let e := QuotientAddGroup.quotientKerEquivOfSurjective p hs
  have hc : Continuous e :=
    (QuotientAddGroup.isQuotientMap_mk p.ker).continuous_iff.mpr hp.continuous
  have ho : IsOpenMap e :=
    QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap_iff.mpr hp.isOpenMap
  exact e.toEquiv.toHomeomorphOfContinuousOpen hc ho

omit [IsTopologicalAddGroup G] in
@[simp]
theorem quotientHomeomorph_mk (p : V →+ G) (hp : IsLocalHomeomorph p)
    (hs : Function.Surjective p) (v : V) :
    quotientHomeomorph p hp hs (QuotientAddGroup.mk v) = p v := rfl

end Groups

/-- A compact quotient forces an additive lattice to span the ambient real
vector space. Otherwise a nonzero real functional would descend to the compact
quotient and map it continuously onto the noncompact real line. -/
theorem real_span_eq_top_of_compact_quotient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V)
    [CompactSpace (V ⧸ Λ.toAddSubgroup)] :
    Submodule.span ℝ (Λ : Set V) = ⊤ := by
  by_contra h
  obtain ⟨φ, hφ, hker⟩ :=
    (Submodule.span ℝ (Λ : Set V)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr h)
  let f : (V ⧸ Λ.toAddSubgroup) →+ ℝ :=
    QuotientAddGroup.lift Λ.toAddSubgroup φ.toAddMonoidHom
      (fun v hv => hker (Submodule.subset_span hv))
  have hf : Continuous f :=
    (QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).continuous_iff.mpr
      φ.continuous_of_finiteDimensional
  have hsφ : Function.Surjective φ := by
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hφ
    have hv' : φ v ≠ 0 := hv
    intro r
    refine ⟨(r / φ v) • v, ?_⟩
    simp only [map_smul, smul_eq_mul, div_mul_cancel₀ r hv']
  have hsf : Function.Surjective f := by
    intro r
    obtain ⟨v, hv⟩ := hsφ r
    exact ⟨QuotientAddGroup.mk v, hv⟩
  let : CompactSpace ℝ := hsf.compactSpace hf
  exact noncompact_univ ℝ isCompact_univ

/-- Once the local exponential map is constructed, its kernel is a full
discrete lattice. This proves the cocompactness-to-fullness step explicitly. -/
theorem kernel_is_lattice
    {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ConnectedSpace G] [CompactSpace G]
    (p : V →+ G) (hp : IsLocalHomeomorph p) :
    ∃ h : DiscreteTopology p.ker.toIntSubmodule,
      @IsZLattice ℝ _ V _ _ p.ker.toIntSubmodule h := by
  have hs := surjective_of_localHomeomorph p hp
  have hcompact : CompactSpace (V ⧸ p.ker) :=
    (quotientHomeomorph p hp hs).symm.surjective.compactSpace
      (quotientHomeomorph p hp hs).symm.continuous
  let : CompactSpace (V ⧸ p.ker.toIntSubmodule.toAddSubgroup) := by
    exact Eq.mpr (congrArg (fun K : AddSubgroup V => CompactSpace (V ⧸ K))
      (AddSubgroup.toIntSubmodule_toAddSubgroup p.ker)) hcompact
  let : DiscreteTopology p.ker.toIntSubmodule := kernel_discrete p hp
  exact ⟨inferInstance, ⟨real_span_eq_top_of_compact_quotient p.ker.toIntSubmodule⟩⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.UniformizationEq.Constructions.Uniformization
