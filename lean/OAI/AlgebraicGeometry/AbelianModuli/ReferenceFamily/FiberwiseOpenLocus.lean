import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Sets.Opens

/-! # Fiberwise Open Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiberwiseOpenLocus

/-! A closed family map has an open locus where each whole fiber
lies in a specified open. For an open family map and a clopen
condition this locus is also closed. Its base-change criterion
retains the actual lifting of pairs of fiber points. -/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsClosedMap f) (U : TopologicalSpace.Opens X)

def fiberwiseOpenLocus : TopologicalSpace.Opens Y :=
  ⟨(f '' (U : Set X)ᶜ)ᶜ, (hf _ U.isOpen.isClosed_compl).isOpen_compl⟩

theorem fiberwiseOpenLocus_mem_iff (y : Y) :
    y ∈ fiberwiseOpenLocus f hf U ↔ ∀ x, f x = y → x ∈ U := by
  constructor
  · intro hy x hx
    by_contra h
    exact hy ⟨x, h, hx⟩
  · intro hy
    rintro ⟨x, hx, rfl⟩
    exact hx (hy x rfl)

theorem fiberwiseOpenLocus_preimage :
    f ⁻¹' (fiberwiseOpenLocus f hf U : Set Y) ⊆ U := by
  intro x hx
  exact (fiberwiseOpenLocus_mem_iff f hf U (f x)).mp hx x rfl

theorem fiberwiseOpenLocus_isClosed (ho : IsOpenMap f) (hU : IsClosed (U : Set X)) :
    IsClosed (fiberwiseOpenLocus f hf U : Set Y) :=
  (ho _ hU.isOpen_compl).isClosed_compl

theorem fiberwiseOpenLocus_baseChange {T Z : Type*}
    (p : Z → X) (g : Z → T) (q : T → Y)
    (hcomm : ∀ z, f (p z) = q (g z))
    (hlift : ∀ x t, f x = q t → ∃ z, p z = x ∧ g z = t) :
    Set.range q ⊆ fiberwiseOpenLocus f hf U ↔ ∀ z, p z ∈ U := by
  constructor
  · intro h z
    exact (fiberwiseOpenLocus_mem_iff f hf U (q (g z))).mp
      (h ⟨g z, rfl⟩) (p z) (hcomm z)
  · intro h y hy
    obtain ⟨t, rfl⟩ := hy
    apply (fiberwiseOpenLocus_mem_iff f hf U (q t)).mpr
    intro x hx
    obtain ⟨z, hz, _⟩ := hlift x t hx
    exact hz ▸ h z

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiberwiseOpenLocus
