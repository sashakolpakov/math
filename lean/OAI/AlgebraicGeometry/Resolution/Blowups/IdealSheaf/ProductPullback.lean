import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealSheafIdentification
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.OpenIdealSheafUniqueness

/-! # Product Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductPullback.Construction

noncomputable section

/-! Products and powers of native ideal sheaves commute with arbitrary scheme pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem idealSheaf_comap_mul_affineMap {X : Scheme.{u}} (I J : X.IdealSheafData)
    (U : X.affineOpens) {S : Type u} [CommRing S] (φ : Γ(X, U) →+* S) :
    (I * J).comap (Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec) =
      I.comap (Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec) *
        J.comap (Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec) := by
  rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel,
    Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel, Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel]
  change Affine.QuotientKernel.Construction.affineQuotientKernel (((I.ideal U) * (J.ideal U)).map φ) =
    Affine.QuotientKernel.Construction.affineQuotientKernel ((I.ideal U).map φ) * Affine.QuotientKernel.Construction.affineQuotientKernel ((J.ideal U).map φ)
  rw [Ideal.map_mul, ProductRestriction.Construction.affineQuotientKernel_mul]

theorem exists_affine_pair_at_point {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) :
    ∃ (U : X.affineOpens) (V : Y.affineOpens), V.1 ≤ f ⁻¹ᵁ U.1 ∧ y ∈ V.1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (f ⁻¹ᵁ U).isOpen
  exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hVU, hyV⟩

theorem idealSheaf_comap_mul {X Y : Scheme.{u}} (I J : X.IdealSheafData) (f : Y ⟶ X) :
    (I * J).comap f = I.comap f * J.comap f := by
  classical
  choose U V hsub hmem using exists_affine_pair_at_point f
  let : ∀ y : Y, IsOpenImmersion (V y).2.fromSpec := fun y => (V y).2.isOpenImmersion_fromSpec
  have hcover : ⨆ y : Y, ((V y).2.fromSpec).opensRange = ⊤ := by
    apply top_le_iff.mp
    intro y _
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨y, ?_⟩
    rw [(V y).2.opensRange_fromSpec]
    exact hmem y
  apply Finite.OpenIdealSheafUniqueness.Construction.idealSheaf_eq_of_open_affine_restrictions
    (fun y : Y => Spec (.of Γ(Y, V y))) (fun y => (V y).2.fromSpec) hcover
  intro y
  rw [ProductRestriction.Construction.idealSheaf_comap_mul_open (I.comap f) (J.comap f) (V y).2.fromSpec,
    ← Scheme.IdealSheafData.comap_comp (I * J) (V y).2.fromSpec f,
    ← Scheme.IdealSheafData.comap_comp I (V y).2.fromSpec f,
    ← Scheme.IdealSheafData.comap_comp J (V y).2.fromSpec f,
    ← IsAffineOpen.SpecMap_appLE_fromSpec f (U y).2 (V y).2 (hsub y)]
  exact idealSheaf_comap_mul_affineMap I J (U y) (f.appLE (U y).1 (V y).1 (hsub y)).hom

theorem idealSheaf_comap_pow {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) (n : ℕ) :
    (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => simp only [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, idealSheaf_comap_mul, ih, pow_succ]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductPullback.Construction
