import OAI.Analysis.PDE.Dirichlet.Periodic.Maximum
import Mathlib.Algebra.Module.ZLattice.Basic

open Set Module
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Reduce the periodic coordinates modulo any full lattice, leaving the
transverse coordinates unchanged. -/
def latticeRepresentative (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (x : E) : E :=
  e.symm (ZSpan.fract b (e x).1, (e x).2)

/-- Periodicity only in the first factor of the chosen coordinate splitting. -/
def LatticePeriodic {W : Type*} (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (f : E → W) : Prop :=
  ∀ (x : E) (l : Submodule.span ℤ (Set.range b)),
    f (e.symm ((e x).1 + (l : P), (e x).2)) = f x

theorem LatticePeriodic.representative {W : Type*} {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    {f : E → W} (hf : LatticePeriodic e b f) (x : E) :
    f (latticeRepresentative e b x) = f x := by
  simpa only [latticeRepresentative, ZSpan.fract_apply, Submodule.coe_neg, sub_eq_add_neg]
    using hf x (-ZSpan.floor b (e x).1)

/-- A compact fundamental cell cut out by the physical domain. -/
def latticeSublevelCell (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (C : Set V)
    (r : E → ℝ) : Set E :=
  e.symm '' ((parallelepiped b) ×ˢ C) ∩ {x | r x ≤ 0}

theorem isCompact_latticeSublevelCell (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : E → ℝ} (hr : Continuous r) :
    IsCompact (latticeSublevelCell e b C r) := by
  apply IsCompact.inter_right _ (isClosed_le hr continuous_const)
  exact (b.parallelepiped.isCompact.prod hC).image e.symm.continuous

theorem latticeRepresentative_mem_sublevelCell (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} {r : E → ℝ} (hr : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C) {x : E} (hx : r x ≤ 0) :
    latticeRepresentative e b x ∈ latticeSublevelCell e b C r := by
  constructor
  · refine ⟨(ZSpan.fract b (e x).1, (e x).2), ⟨?_, hbounded x hx⟩, rfl⟩
    exact ZSpan.fundamentalDomain_subset_parallelepiped b
      (ZSpan.fract_mem_fundamentalDomain b (e x).1)
  · change r (latticeRepresentative e b x) ≤ 0
    rw [hr.representative]
    exact hx

/-- The periodic maximum principle with the representative map and compact
cell constructed from an arbitrary lattice basis. -/
theorem maximum_principle_lattice
    {κ : Type*} [Fintype κ] {a : E → κ → ℝ} {v : E → κ → E}
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r f : E → ℝ} {M : ℝ}
    (hr : ContDiff ℝ 2 r) (hf : ContDiff ℝ 2 f)
    (hrper : LatticePeriodic e b r) (hfper : LatticePeriodic e b f)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (ha : ∀ x, r x < 0 → ∀ i, 0 ≤ a x i)
    (hL : ∀ x, r x < 0 → 0 ≤ ellipticValue a v f x)
    (hrL : ∀ x, r x < 0 → 0 < ellipticValue a v r x)
    (hbd : ∀ x, r x = 0 → f x ≤ M) : ∀ x, r x ≤ 0 → f x ≤ M := by
  apply maximum_principle_representatives (a := a) (v := v) (latticeRepresentative e b)
    (isCompact_latticeSublevelCell e b hC hr.continuous) inter_subset_right hr hf
  · exact fun x hx ↦ latticeRepresentative_mem_sublevelCell e b hrper hbounded hx
  · exact fun x _ ↦ hrper.representative x
  · exact fun x _ ↦ hfper.representative x
  · exact ha
  · exact hL
  · exact hrL
  · exact hbd

end OAI.Analysis.PDE.Dirichlet
