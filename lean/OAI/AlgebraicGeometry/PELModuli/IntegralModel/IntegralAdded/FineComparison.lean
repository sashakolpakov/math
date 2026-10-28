import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.Classification

/-! # Fine Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineComparison

noncomputable section

/-! Fine classification on reduced tests identifies the actual parameter
schemes and their universal PEL families with both ordered levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R}

theorem integralAddedPEL_fine_comparison
    (V W : Over (Spec (.of R))) [IsReduced V.left] [IsReduced W.left]
    (U : PELId.IntegralAddedPELLevel P R iotaO L N V)
    (A : PELId.IntegralAddedPELLevel P R iotaO L N W)
    (hU : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (B : PELId.IntegralAddedPELLevel P R iotaO L N T),
      ∃! f : T ⟶ V, Nonempty (PELId.IntegralAddedPELLevel.Iso (U.pullback f) B))
    (hA : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (B : PELId.IntegralAddedPELLevel P R iotaO L N T),
      ∃! f : T ⟶ W, Nonempty (PELId.IntegralAddedPELLevel.Iso (A.pullback f) B)) :
    ∃ e : V ≅ W, Nonempty (PELId.IntegralAddedPELLevel.Iso (A.pullback e.hom) U) := by
  obtain ⟨f, ⟨ef⟩, _⟩ := hA V U
  obtain ⟨g, ⟨eg⟩, _⟩ := hU W A
  have hfg : f ≫ g = 𝟙 V := by
    obtain ⟨q, _, hq⟩ := hU V U
    exact (hq (f ≫ g) ⟨(U.pullbackCompIso g f).symm.trans ((eg.pullback f).trans ef)⟩).trans
      (hq (𝟙 V) ⟨U.pullbackIdIso⟩).symm
  have hgf : g ≫ f = 𝟙 W := by
    obtain ⟨q, _, hq⟩ := hA W A
    exact (hq (g ≫ f) ⟨(A.pullbackCompIso f g).symm.trans ((ef.pullback g).trans eg)⟩).trans
      (hq (𝟙 W) ⟨A.pullbackIdIso⟩).symm
  exact ⟨⟨f, g, hfg, hgf⟩, ⟨ef⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineComparison
