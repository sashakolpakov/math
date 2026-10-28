import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineGroupoidIs

/-! # Affine Basis -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineBasis.Construction.AffineBasisTransfer

/-! # Transport of affine source bases along pullbacks and arrow isomorphisms -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem of_isPullback {H S Y X : Scheme.{u}}
    [IsAffine H] [IsAffine S] [IsAffine Y] [IsAffine X]
    (h : H ⟶ S) (a : X ⟶ S) (r : Y ⟶ H) (s : Y ⟶ X)
    (hs : IsPullback r s h a) {ι : Type v}
    (b : letI := h.appTop.hom.toAlgebra; Module.Basis ι Γ(S, ⊤) Γ(H, ⊤)) :
    letI := s.appTop.hom.toAlgebra
    Nonempty (Module.Basis ι Γ(X, ⊤) Γ(Y, ⊤)) := by
  obtain ⟨b', _⟩ := AffineGroupoidIs.Construction.AffineGroupoid.exists_basis_of_isPushout
    h.appTop a.appTop r.appTop s.appTop (isPushout_appTop_of_isPullback hs) b
  exact ⟨b'⟩

theorem of_arrowIso {H S Y X : Scheme.{u}}
    [IsAffine H] [IsAffine S] [IsAffine Y] [IsAffine X]
    {h : H ⟶ S} {s : Y ⟶ X} (e : Arrow.mk h ≅ Arrow.mk s) {ι : Type v}
    (b : letI := h.appTop.hom.toAlgebra; Module.Basis ι Γ(S, ⊤) Γ(H, ⊤)) :
    letI := s.appTop.hom.toAlgebra
    Nonempty (Module.Basis ι Γ(X, ⊤) Γ(Y, ⊤)) := by
  exact of_isPullback (H := H) (S := S) (Y := Y) (X := X) h e.inv.right e.inv.left s
    (IsPullback.of_horiz_isIso ⟨e.inv.w⟩) b

/-- A basis on one affine open restricts to every smaller affine open. -/
theorem restrictLE {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (U V : S.Opens) [IsAffine U] [IsAffine V] (hUV : U ≤ V) {ι : Type v}
    (b : letI := (f ∣_ V).appTop.hom.toAlgebra;
      Module.Basis ι Γ(V.toScheme, ⊤) Γ((f ⁻¹ᵁ V).toScheme, ⊤)) :
    letI := (f ∣_ U).appTop.hom.toAlgebra
    Nonempty (Module.Basis ι Γ(U.toScheme, ⊤) Γ((f ⁻¹ᵁ U).toScheme, ⊤)) := by
  have : IsAffine (f ⁻¹ᵁ U).toScheme := isAffine_of_isAffineHom (f ∣_ U)
  have : IsAffine (f ⁻¹ᵁ V).toScheme := isAffine_of_isAffineHom (f ∣_ V)
  have hp : IsPullback (X.homOfLE (f.preimage_mono hUV)) (f ∣_ U)
      (f ∣_ V) (S.homOfLE hUV) := by
    apply IsPullback.of_right (t := (isPullback_morphismRestrict f V).flip)
    · simpa only [Scheme.homOfLE_ι] using (isPullback_morphismRestrict f U).flip
    · exact (morphismRestrict_homOfLE f U V hUV).symm
  exact of_isPullback (f ∣_ V) (S.homOfLE hUV) (X.homOfLE (f.preimage_mono hUV))
    (f ∣_ U) hp b

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineBasis.Construction.AffineBasisTransfer
