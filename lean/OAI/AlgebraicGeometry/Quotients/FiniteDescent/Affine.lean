import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineBasis
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineQuotientOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantOpensEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantAffineHas
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantNeighborhood

/-! # Affine -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Affine.Construction.AffineFiniteDescent

/-!
# Affineness descends along a finite-free cover

For a cover obtained by base change from a finite-free affine morphism, the
affine relation quotient identifies the target with an affine spectrum.
This will allow affine neighborhoods constructed after a finite base change
to descend to the original abelian scheme.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem isAffine_of_cover
    {H S Y X : Scheme.{u}} [IsAffine H] [IsAffine S] [IsAffine Y]
    (h : H ⟶ S) (a : X ⟶ S) (r : Y ⟶ H) (q : Y ⟶ X)
    (hq : IsPullback r q h a) [IsFinite h] [Flat q] [Surjective q]
    {ι : Type v} [Fintype ι]
    (b : letI := h.appTop.hom.toAlgebra; Module.Basis ι Γ(S, ⊤) Γ(H, ⊤)) :
    IsAffine X := by
  classical
  have : IsFinite q := MorphismProperty.of_isPullback hq inferInstance
  let s : pullback q q ⟶ Y := pullback.fst q q
  let t : pullback q q ⟶ Y := pullback.snd q q
  have : IsAffine (pullback q q) := isAffine_of_isAffineHom s
  have hk : IsKernelPair q s t := IsPullback.of_hasPullback q q
  let e := hk.equivalenceRelation q s t (pullback.isLimit t s)
  have hp : IsPullback (t ≫ r) s h (q ≫ a) := hk.flip.paste_horiz hq
  obtain ⟨bR⟩ := AffineBasis.Construction.AffineBasisTransfer.of_isPullback h (q ≫ a) (t ≫ r) s hp b
  obtain ⟨hfin, hflat, _, hsurj, hk'⟩ :=
    AffineQuotientOf.Construction.AffineQuotient.projection_properties_of_finiteFree_absolute s t e bR
  let := hfin
  let := hflat
  let := hsurj
  obtain ⟨eQ, _, _⟩ := Quotient.Construction.QuotientDescent.existsUnique_iso (AffineQuotientOf.Construction.AffineQuotient.projection s t) q hk' hk
  exact (IsAffine.iff_of_isIso eQ.inv).mpr inferInstance

/-- An affine neighborhood of the full preimage of a finite set descends
to an affine neighborhood of that set along a finite-free cover. -/
theorem exists_affine_neighborhood
    {H S Y X : Scheme.{u}} [IsAffine H] [IsAffine S]
    (h : H ⟶ S) (a : X ⟶ S) (r : Y ⟶ H) (q : Y ⟶ X)
    (hq : IsPullback r q h a) [IsFinite h] [Flat q] [Surjective q]
    {n : ℕ}
    (b : letI := h.appTop.hom.toAlgebra; Module.Basis (Fin n) Γ(S, ⊤) Γ(H, ⊤))
    (F : Set X) (hF : F.Finite) (U : Y.Opens) (hU : IsAffineOpen U)
    (hFU : q ⁻¹' F ⊆ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ F ⊆ V ∧ q ⁻¹ᵁ V ≤ U := by
  have : IsFinite q := MorphismProperty.of_isPullback hq inferInstance
  let s : pullback q q ⟶ Y := pullback.fst q q
  let t : pullback q q ⟶ Y := pullback.snd q q
  have hk : IsKernelPair q s t := IsPullback.of_hasPullback q q
  let e := hk.equivalenceRelation q s t (pullback.isLimit t s)
  have hp : IsPullback (t ≫ r) s h (q ≫ a) := hk.flip.paste_horiz hq
  have hFs : ∀ x ∈ q ⁻¹' F, ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ q ⁻¹' F := by
    rintro x hx y ⟨z, hz, hz'⟩
    have he : q x = q y := by
      simpa only [Scheme.Hom.comp_apply, hz, hz'] using congrArg (fun f => f z) hk.w
    change q y ∈ F
    exact he ▸ hx
  obtain ⟨W, hW, hWU, hWi, hFW⟩ := InvariantNeighborhood.Construction.FiniteInvariantNeighborhood.exists_invariant_affine e
    (q ⁻¹' F) (q.finite_preimage hF) hFs U hU hFU (by
      intro D hD _
      let : IsAffine D := hD
      exact ⟨n, InvariantAffineHas.Construction.InvariantAffineBasis.exists_basis_restrict h (q ≫ a) (t ≫ r) s hp b D⟩)
  let : IsAffine W := hW
  let V := InvariantOpensEq.Construction.InvariantOpens.descend q hk W hWi
  let qW : W.toScheme ⟶ V.toScheme := InvariantOpensEq.Construction.InvariantOpens.restrictProjection q hk W hWi
  have hqW : IsPullback (W.ι ≫ r) qW h (V.ι ≫ a) :=
    (InvariantOpensEq.Construction.InvariantOpens.restrictProjection_isPullback q hk W hWi).flip.paste_horiz hq
  have : Flat qW := inferInstanceAs (Flat (InvariantOpensEq.Construction.InvariantOpens.restrictProjection q hk W hWi))
  have : Surjective qW := inferInstanceAs (Surjective (InvariantOpensEq.Construction.InvariantOpens.restrictProjection q hk W hWi))
  refine ⟨V, isAffine_of_cover h (V.ι ≫ a) (W.ι ≫ r) qW hqW b, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy⟩ := q.surjective x
    exact ⟨y, hFW (by simpa only [Set.mem_preimage, hy] using hx), hy⟩
  · change q ⁻¹ᵁ InvariantOpensEq.Construction.InvariantOpens.descend q hk W hWi ≤ U
    rw [InvariantOpensEq.Construction.InvariantOpens.preimage_descend]
    exact hWU

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Affine.Construction.AffineFiniteDescent
