import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantAffineEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineGroupoidIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantCoverHas

/-! # Invariant Affine Has -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantAffineHas.Construction.InvariantAffineBasis

/-!
# Invariant neighborhoods for relations pulled back from a finite-free map

For a finite subgroup action the relation source is the base change of the
subgroup's structure map. A basis on the base therefore supplies every basis
required in the norm neighborhood construction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {H S R X : Scheme.{u}} [IsAffine H] [IsAffine S]
variable (h : H ⟶ S) (a : X ⟶ S) (r : R ⟶ H) (s : R ⟶ X)
variable (hs : IsPullback r s h a) [IsFinite h]

include hs

/-- An affine restriction of a pulled-back finite-free source has the
base-changed basis, without any assumption on the relation target. -/
theorem exists_basis_restrict {ι : Type v}
    (b : letI := h.appTop.hom.toAlgebra; Module.Basis ι Γ(S, ⊤) Γ(H, ⊤))
    (D : X.Opens) [IsAffine D] :
    letI := (s ∣_ D).appTop.hom.toAlgebra
    Nonempty (Module.Basis ι Γ(D.toScheme, ⊤) Γ((s ⁻¹ᵁ D).toScheme, ⊤)) := by
  have : IsFinite s := MorphismProperty.of_isPullback hs inferInstance
  have : IsAffine (s ⁻¹ᵁ D).toScheme := isAffine_of_isAffineHom (s ∣_ D)
  have hp : IsPullback ((s ⁻¹ᵁ D).ι ≫ r) (s ∣_ D) h (D.ι ≫ a) :=
    (isPullback_morphismRestrict s D).flip.paste_horiz hs
  obtain ⟨bD, _⟩ := AffineGroupoidIs.Construction.AffineGroupoid.exists_basis_of_isPushout
    h.appTop (D.ι ≫ a).appTop ((s ⁻¹ᵁ D).ι ≫ r).appTop (s ∣_ D).appTop
    (isPushout_appTop_of_isPullback hp) b
  exact ⟨bD⟩

/-- The norm construction applies to a finite orbit in an affine open as
soon as the source comes by base change from one finite-free affine map. -/
theorem exists_invariant_affine
    {n : ℕ} (b : letI := h.appTop.hom.toAlgebra; Module.Basis (Fin n) Γ(S, ⊤) Γ(H, ⊤))
    (t : R ⟶ X) (e : CategoryTheory.EquivalenceRelation s t)
    (x : X) (U : X.Opens) (hU : IsAffineOpen U)
    (hUx : ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ W ≤ U ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W ∧
      ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ W := by
  have : IsFinite s := MorphismProperty.of_isPullback hs inferInstance
  apply InvariantAffineEq.Construction.InvariantAffine.exists_invariant_affine e x U hU hUx
  intro D hD _
  let : IsAffine D := hD
  exact ⟨n, exists_basis_restrict h a r s hs b D⟩

/-- Affine neighborhoods of whole orbits supply all invariant affine
refinements, by prime avoidance followed by the norm construction. -/
theorem hasAffineRefinements
    {n : ℕ} (b : letI := h.appTop.hom.toAlgebra; Module.Basis (Fin n) Γ(S, ⊤) Γ(H, ⊤))
    (t : R ⟶ X) (e : CategoryTheory.EquivalenceRelation s t)
    (hOrbit : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧
      ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ U) :
    InvariantCoverHas.Construction.InvariantCover.HasAffineRefinements s t := by
  have : IsFinite s := MorphismProperty.of_isPullback hs inferInstance
  intro V hV x hx
  obtain ⟨U, hU, hUx⟩ := hOrbit x
  have hVx : {y | Invariant.Construction.InvariantCore.Related s t x y} ⊆ V := by
    rintro y ⟨z, hz, hz'⟩
    have hmem : z ∈ s ⁻¹ᵁ V := by simpa only [Scheme.Hom.mem_preimage, hz] using hx
    rw [hV] at hmem
    change y ∈ V
    simpa only [Scheme.Hom.mem_preimage, hz'] using hmem
  obtain ⟨U', hU', hFU', _, hU'V⟩ := AffineNeighborhoodOpen.Construction.AffineNeighborhood.exists_affineOpen_subset X
    {y | Invariant.Construction.InvariantCore.Related s t x y} (Invariant.Construction.InvariantCore.finite_orbit s t x) U V hU hUx hVx
  obtain ⟨W, hW, hWU', hWi, hWx⟩ :=
    exists_invariant_affine h a r s hs b t e x U' hU' (fun _ hy => hFU' hy)
  exact ⟨⟨W, hW, hWi⟩, hWx x (Invariant.Construction.InvariantCore.related_refl e x), hWU'.trans hU'V⟩

/-- The actual scheme quotient exists when the finite-free relation source
comes from the affine base and every orbit has an affine neighborhood. -/
theorem exists_quotient
    {n : ℕ} (b : letI := h.appTop.hom.toAlgebra; Module.Basis (Fin n) Γ(S, ⊤) Γ(H, ⊤))
    (t : R ⟶ X) (e : CategoryTheory.EquivalenceRelation s t)
    (hOrbit : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧
      ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ U) :
    ∃ (Q : Scheme.{u}) (π : X ⟶ Q),
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧ Surjective π ∧
      IsKernelPair π s t ∧
      ∀ (T : Scheme.{u}) (f : X ⟶ T), s ≫ f = t ≫ f →
        ∃! g : Q ⟶ T, π ≫ g = f := by
  have : IsFinite s := MorphismProperty.of_isPullback hs inferInstance
  apply InvariantCoverHas.Construction.InvariantCover.exists_quotient e (hasAffineRefinements h a r s hs b t e hOrbit)
  intro U
  let : IsAffine U.val := U.property.1
  exact ⟨n, exists_basis_restrict h a r s hs b U.val⟩

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantAffineHas.Construction.InvariantAffineBasis
