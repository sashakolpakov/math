import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualizerFiberLocus

/-! # Fiber Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.FiberEquality

noncomputable section

/-! Local equality near equal fibers propagates over a connected base when the family map is open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S Y : Scheme.{u}}

theorem equalizerFiberLocus_isOpen_of_localEquality (p : X ⟶ S) (f g : X ⟶ Y)
    (hlocal : ∀ s ∈ EqualizerFiberLocus.equalizerFiberLocus p f g, ∃ V : S.Opens, s ∈ V ∧
      (p ⁻¹ᵁ V).ι ≫ f = (p ⁻¹ᵁ V).ι ≫ g) : IsOpen (EqualizerFiberLocus.equalizerFiberLocus p f g) := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  obtain ⟨V, hsV, hV⟩ := hlocal s hs
  exact Filter.mem_of_superset (V.isOpen.mem_nhds hsV)
    (EqualizerFiberLocus.restrictionEq_le_equalizerFiberLocus p f g V hV)

theorem connectedFamily_eq_of_localEquality (p : X ⟶ S) (hp : IsOpenMap p)
    [PreconnectedSpace S] (f g : X ⟶ Y) [Y.IsSeparated]
    (hlocal : ∀ s ∈ EqualizerFiberLocus.equalizerFiberLocus p f g, ∃ V : S.Opens, s ∈ V ∧
      (p ⁻¹ᵁ V).ι ≫ f = (p ⁻¹ᵁ V).ι ≫ g)
    (hstart : (EqualizerFiberLocus.equalizerFiberLocus p f g).Nonempty) : f = g := by
  have hall : EqualizerFiberLocus.equalizerFiberLocus p f g = Set.univ :=
    IsClopen.eq_univ ⟨EqualizerFiberLocus.equalizerFiberLocus_isClosed p hp f g,
      equalizerFiberLocus_isOpen_of_localEquality p f g hlocal⟩ hstart
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨V, hx, hV⟩ := hlocal (p x) (by rw [hall]; trivial)
  exact ⟨p ⁻¹ᵁ V, hx, hV⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.FiberEquality
