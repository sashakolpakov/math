import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Invariant
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Quotient Affine Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.QuotientAffineCover

noncomputable section

/-! A finite quotient gives an invariant affine cover of its source.
On a compact source a finite such cover is chosen. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem finite_invariant_affine_cover_of_finite_map {X Q R : Scheme.{0}}
    [CompactSpace X] (q : X ⟶ Q) [IsFinite q] (s t : R ⟶ X) (h : s ≫ q = t ≫ q) :
    ∃ (I : Type) (_ : Finite I) (V : I → X.Opens),
      (∀ i, IsAffineOpen (V i)) ∧ (∀ i, s ⁻¹ᵁ V i = t ⁻¹ᵁ V i) ∧ iSup V = ⊤ := by
  classical
  let V (i : Q.affineCover.I₀) := q ⁻¹ᵁ (Q.affineCover.f i).opensRange
  have hV (i) : IsAffineOpen (V i) := (isAffineOpen_opensRange (Q.affineCover.f i)).preimage q
  have hc : ∀ x : X, ∃ i, x ∈ V i := by
    intro x
    exact ⟨Q.affineCover.idx (q x), Q.affineCover.covers (q x)⟩
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover (fun i => (V i : Set X))
    (fun i => (V i).isOpen) (by intro x _; exact Set.mem_iUnion.mpr (hc x))
  refine ⟨J, inferInstance, fun i => V i, fun i => hV i, ?_, ?_⟩
  · intro i
    exact (Scheme.Hom.comp_preimage s q _).symm.trans
      ((congrArg (fun f : R ⟶ Q => f ⁻¹ᵁ (Q.affineCover.f i).opensRange) h).trans
        (Scheme.Hom.comp_preimage t q _))
  · apply top_le_iff.mp
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hJ (Set.mem_univ x))
    obtain ⟨hiJ, hxi⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨⟨i, hiJ⟩, hxi⟩

theorem affine_orbits_of_invariant_cover {X R : Scheme.{0}} (s t : R ⟶ X)
    {I : Type} (V : I → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hInv : ∀ i, s ⁻¹ᵁ V i = t ⁻¹ᵁ V i) (hcover : iSup V = ⊤) :
    ∀ x : X, ∃ W : X.Opens, IsAffineOpen W ∧
      ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related s t x y → y ∈ W := by
  intro x
  have hx : x ∈ iSup V := hcover ▸ Set.mem_univ x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨V i, hV i, ?_⟩
  rintro y ⟨r, hr, ht⟩
  have hh : r ∈ s ⁻¹ᵁ V i := by simpa only [Scheme.Hom.mem_preimage, hr] using hi
  rw [hInv i] at hh
  simpa only [Scheme.Hom.mem_preimage, ht] using hh

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.QuotientAffineCover
