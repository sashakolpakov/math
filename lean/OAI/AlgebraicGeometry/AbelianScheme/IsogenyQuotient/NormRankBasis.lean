import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormFrameBasis
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeTrivializationBasis
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Norm Rank Basis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormRankBasis.Construction

noncomputable section

/-! The actual finite-flat rank supplies the fixed-size bases needed
for the norm charts. No reducedness or characteristic assumption is used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}}

theorem affine_finrank_eq_basis_card [IsAffine X] [IsAffine Y]
    (q : X ⟶ Y) [IsFinite q] [Flat q] {d : ℕ}
    (b : letI := q.appTop.hom.toAlgebra; Module.Basis (Fin d) Γ(Y, ⊤) Γ(X, ⊤))
    (y : Y) : q.finrank y = d := by
  let := q.appTop.hom.toAlgebra
  have : Module.Free Γ(Y, ⊤) Γ(X, ⊤) := Module.Free.of_basis b
  have : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := Module.Finite.of_basis b
  have : Nontrivial Γ(Y, ⊤) := (Y.isoSpec.hom y).nontrivial
  have : IsFinite (Spec.map q.appTop) := (IsFinite.SpecMap_iff _).mpr q.finite_appTop
  have : Flat (Spec.map q.appTop) := Flat.SpecMap_iff.mpr q.flat_appTop
  have hp : IsPullback X.isoSpec.hom q (Spec.map q.appTop) Y.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality q⟩
  calc
    q.finrank y = (Spec.map q.appTop).finrank (Y.isoSpec.hom y) :=
      Scheme.Hom.finrank_of_isPullback _ _ _ _ hp y
    _ = Module.rankAtStalk (R := Γ(Y, ⊤)) Γ(X, ⊤) (Y.isoSpec.hom y) :=
      Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, ⊤) Γ(X, ⊤) _
    _ = d := by
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis b]
      exact Fintype.card_fin d

theorem exists_fixed_rank_basis_neighborhood (q : X ⟶ Y)
    [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] (d : ℕ)
    (hdegree : ∀ y : Y, q.finrank y = d) (y : Y) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U ∧
      letI := (q ∣_ U).appTop.hom.toAlgebra
      Nonempty (Module.Basis (Fin d) Γ(U.toScheme, ⊤) Γ((q ⁻¹ᵁ U).toScheme, ⊤)) := by
  obtain ⟨U, hU, hy, n, ⟨b⟩⟩ := Quotients.FiniteDescent.SchemeTrivializationBasis.Construction.SchemeTrivialization.exists_basis_neighborhood q y
  have : IsAffine U.toScheme := hU
  have : IsAffine (q ⁻¹ᵁ U).toScheme := isAffine_of_isAffineHom (q ∣_ U)
  have hn : n = d := (affine_finrank_eq_basis_card (q ∣_ U) b ⟨y, hy⟩).symm.trans
    ((Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict q U).flip ⟨y, hy⟩).trans
      (hdegree y))
  subst n
  exact ⟨U, hU, hy, ⟨b⟩⟩

theorem normFrameOpens_cover_of_finrank (q : X ⟶ Y)
    [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (d : ℕ)
    (hdegree : ∀ y : Y, q.finrank y = d) (y : Y) :
    ∃ U : LocalNormSections.Construction.NormFrameOpen q L d, y ∈ U.openSet := by
  obtain ⟨U, hU, hyU, ⟨b⟩⟩ := exists_fixed_rank_basis_neighborhood q d hdegree y
  obtain ⟨V, hyV, ⟨e⟩⟩ := L.locallyTrivial y
  obtain ⟨_, ⟨W : Y.Opens, hW, rfl⟩, hyW, hWU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ U ⊓ V from ⟨hyU, hyV⟩)
      (U ⊓ V).isOpen
  have : IsAffine U.toScheme := hU
  have : IsAffine W.toScheme := hW
  obtain ⟨bW⟩ := Quotients.FiniteDescent.AffineBasis.Construction.AffineBasisTransfer.restrictLE q W U (hWU.trans inf_le_left) b
  exact ⟨⟨W, hW, bW, (L.frameRestrict (hWU.trans inf_le_right) e).symm⟩, hyW⟩

theorem normFrameOpens_cover_connected (q : X ⟶ Y)
    [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] [PreconnectedSpace Y]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (y₀ y : Y) :
    ∃ U : LocalNormSections.Construction.NormFrameOpen q L (q.finrank y₀), y ∈ U.openSet :=
  normFrameOpens_cover_of_finrank q L (q.finrank y₀)
    (fun y => q.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace y y₀) y

theorem finiteFlat_surjective_rank_pos (q : X ⟶ Y)
    [IsFinite q] [Flat q] [Surjective q] (y : Y) : 0 < q.finrank y :=
  (Scheme.Hom.one_le_finrank_iff_surjective q).mpr inferInstance y

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormRankBasis.Construction
