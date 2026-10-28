import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineQuotientOf

/-! # Affine Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AffineDetection.Construction

noncomputable section

/-! Detect affine quotient neighborhoods using their actual finite-free
kernel relation. This retains the given target through the effective
quotient comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem affine_of_finiteFree_kernelPair
    {R X Y : Scheme.{u}} [IsAffine R] [IsAffine X]
    (q : X ⟶ Y) [EffectiveEpi q] (s t : R ⟶ X)
    (hk : IsKernelPair q s t) {ι : Type v} [Fintype ι]
    (b : letI := s.appTop.hom.toAlgebra; Module.Basis ι Γ(X, ⊤) Γ(R, ⊤)) :
    IsAffine Y := by
  classical
  let e := hk.equivalenceRelation q s t (pullback.isLimit t s)
  obtain ⟨hfin, hflat, _, hsurj, hk'⟩ :=
    Quotients.FiniteDescent.AffineQuotientOf.Construction.AffineQuotient.projection_properties_of_finiteFree_absolute s t e b
  have := hfin
  have := hflat
  have := hsurj
  obtain ⟨eQ, _, _⟩ := Quotients.FiniteDescent.Quotient.Construction.QuotientDescent.existsUnique_iso
    (Quotients.FiniteDescent.AffineQuotientOf.Construction.AffineQuotient.projection s t) q hk' hk
  exact (IsAffine.iff_of_isIso eQ.inv).mpr inferInstance

theorem affine_of_kernelPair_source_baseChange
    {H S R X Y : Scheme.{u}} [IsAffine H] [IsAffine S] [IsAffine X]
    (q : X ⟶ Y) [EffectiveEpi q] (s t : R ⟶ X)
    (hk : IsKernelPair q s t) (h : H ⟶ S) [IsFinite h]
    (a : X ⟶ S) (r : R ⟶ H) (hs : IsPullback r s h a)
    {ι : Type v} [Fintype ι]
    (b : letI := h.appTop.hom.toAlgebra; Module.Basis ι Γ(S, ⊤) Γ(H, ⊤)) :
    IsAffine Y := by
  have : IsFinite s := MorphismProperty.of_isPullback hs inferInstance
  have : IsAffine R := isAffine_of_isAffineHom s
  obtain ⟨bR, _⟩ := Quotients.FiniteDescent.AffineGroupoidIs.Construction.AffineGroupoid.exists_basis_of_isPushout h.appTop a.appTop
    r.appTop s.appTop (isPushout_appTop_of_isPullback hs) b
  exact affine_of_finiteFree_kernelPair q s t hk bR

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AffineDetection.Construction
