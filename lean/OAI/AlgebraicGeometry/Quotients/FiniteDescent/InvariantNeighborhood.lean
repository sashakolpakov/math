import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantAffineEq

/-! # Invariant Neighborhood -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantNeighborhood.Construction.FiniteInvariantNeighborhood

/-! # Invariant affine neighborhoods of finite unions of orbits -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R X : Scheme.{u}} {s t : R ⟶ X} [IsFinite s]

theorem exists_norm_data (e : CategoryTheory.EquivalenceRelation s t)
    (F : Set X) (hF : F.Finite)
    (hFs : ∀ x ∈ F, ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ F)
    (U : X.Opens) (hU : IsAffineOpen U) (hFU : F ⊆ U) :
    ∃ D : X.Opens, IsAffineOpen D ∧ D ≤ U ∧ F ⊆ D ∧
      ∃ a : Γ((s ⁻¹ᵁ D).toScheme, ⊤),
        ((s ⁻¹ᵁ D).ι ≫ t) ⁻¹ᵁ D = (s ⁻¹ᵁ D).toScheme.basicOpen a := by
  let : IsAffine U := hU
  have hF' : (U.ι ⁻¹' F).Finite := hF.preimage (f := U.ι) Subtype.val_injective.injOn
  have hFW : U.ι ⁻¹' F ⊆ U.ι ⁻¹ᵁ Invariant.Construction.InvariantCore.core s t U := by
    intro x hx
    exact (Invariant.Construction.InvariantCore.mem_core s t U (U.ι x)).mpr fun y hy => hFU (hFs _ hx y hy)
  obtain ⟨f, hfF, hfW⟩ := AffineNeighborhoodOpen.Construction.AffineNeighborhood.exists_basicOpen_scheme U.toScheme
    (U.ι ⁻¹' F) hF' (U.ι ⁻¹ᵁ Invariant.Construction.InvariantCore.core s t U) hFW
  let D : X.Opens := U.ι ''ᵁ U.toScheme.basicOpen f
  have hD : IsAffineOpen D :=
    ((isAffineOpen_top U.toScheme).basicOpen f).image_of_isOpenImmersion U.ι
  have hDW : D ≤ Invariant.Construction.InvariantCore.core s t U := by
    rintro y ⟨z, hz, rfl⟩
    exact hfW hz
  have hFD : F ⊆ D := fun y hy => ⟨⟨y, hFU hy⟩, hfF hy, rfl⟩
  have htU : s ⁻¹ᵁ D ≤ t ⁻¹ᵁ U := by
    intro r hr
    exact (Invariant.Construction.InvariantCore.mem_core s t U (s r)).mp (hDW hr) (t r) ⟨r, rfl, rfl⟩
  let g : (s ⁻¹ᵁ D).toScheme ⟶ U.toScheme := t.resLE U (s ⁻¹ᵁ D) htU
  refine ⟨D, hD, hDW.trans (Invariant.Construction.InvariantCore.core_le s t e U), hFD, g.appTop f, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι t htU, Scheme.Hom.comp_preimage,
    U.ι.preimage_image_eq, Scheme.preimage_basicOpen_top]

theorem exists_invariant_affine (e : CategoryTheory.EquivalenceRelation s t)
    (F : Set X) (hF : F.Finite)
    (hFs : ∀ x ∈ F, ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ F)
    (U : X.Opens) (hU : IsAffineOpen U) (hFU : F ⊆ U)
    (hb : ∀ (D : X.Opens), IsAffineOpen D → D ≤ U →
      ∃ n : ℕ, letI := (s ∣_ D).appTop.hom.toAlgebra;
        Nonempty (Module.Basis (Fin n) Γ(D.toScheme, ⊤) Γ((s ⁻¹ᵁ D).toScheme, ⊤))) :
    ∃ W : X.Opens, IsAffineOpen W ∧ W ≤ U ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W ∧ F ⊆ W := by
  obtain ⟨D, hD, hDU, hFD, a, ha⟩ := exists_norm_data e F hF hFs U hU hFU
  let : IsAffine D := hD
  have : IsAffine (s ⁻¹ᵁ D).toScheme := isAffine_of_isAffineHom (s ∣_ D)
  obtain ⟨n, ⟨b⟩⟩ := hb D hD hDU
  refine ⟨Invariant.Construction.InvariantCore.core s t D, ?_, (Invariant.Construction.InvariantCore.core_le s t e D).trans hDU,
    Invariant.Construction.InvariantCore.core_invariant s t e D, ?_⟩
  · exact InvariantAffineEq.Construction.InvariantAffine.isAffineOpen_core e D (s ⁻¹ᵁ D).ι (s ∣_ D)
      (isPullback_morphismRestrict s D) b a ha
  · intro x hx
    exact (Invariant.Construction.InvariantCore.mem_core s t D x).mpr fun y hy => hFD (hFs x hx y hy)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantNeighborhood.Construction.FiniteInvariantNeighborhood
