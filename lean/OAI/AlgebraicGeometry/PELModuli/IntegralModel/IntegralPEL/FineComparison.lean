import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.RelativePullback

/-! # Fine Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Equal coefficient embeddings preserve the actual universal data.
Fine classification then compares both the reduced parameter schemes and
their actual integral PEL families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO j : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}

def PEL.Has.IntegralPELObject.changeEmbedding (U : PEL.Has.IntegralPELObject P R iotaO N X) (h : iotaO = j) :
    PEL.Has.IntegralPELObject P R j N X where
  data := U.data
  rosati := U.rosati
  lieRanks := h ▸ U.lieRanks

theorem IntegralPEL.FineComparison.integralPEL_fine_changeEmbedding (U : PEL.Has.IntegralPELObject P R iotaO N X) (h : iotaO = j)
    (hU : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (A : PEL.Has.IntegralPELObject P R iotaO N T),
      ∃! f : T ⟶ X, Nonempty (PEL.Iso.PolarizedActionIso (U.pullback f).data A.data))
    (T : Over (Spec (.of R))) [IsReduced T.left] (A : PEL.Has.IntegralPELObject P R j N T) :
    ∃! f : T ⟶ X, Nonempty (PEL.Iso.PolarizedActionIso ((U.changeEmbedding h).pullback f).data A.data) := by
  obtain ⟨f, ⟨e⟩, hu⟩ := hU T (A.changeEmbedding h.symm)
  exact ⟨f, ⟨e⟩, fun g ⟨a⟩ => hu g ⟨a⟩⟩

theorem IntegralPEL.FineComparison.integralPEL_fine_comparison
    (V W : Over (Spec (.of R))) [IsReduced V.left] [IsReduced W.left]
    (U : PEL.Has.IntegralPELObject P R iotaO N V) (A : PEL.Has.IntegralPELObject P R iotaO N W)
    (hU : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (B : PEL.Has.IntegralPELObject P R iotaO N T),
      ∃! f : T ⟶ V, Nonempty (PEL.Iso.PolarizedActionIso (U.pullback f).data B.data))
    (hA : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (B : PEL.Has.IntegralPELObject P R iotaO N T),
      ∃! f : T ⟶ W, Nonempty (PEL.Iso.PolarizedActionIso (A.pullback f).data B.data)) :
    ∃ e : V ≅ W, Nonempty (PEL.Iso.PolarizedActionIso (A.pullback e.hom).data U.data) := by
  obtain ⟨f, ⟨ef⟩, _⟩ := hA V U
  obtain ⟨g, ⟨eg⟩, _⟩ := hU W A
  have hfg : f ≫ g = 𝟙 V := by
    obtain ⟨q, _, hq⟩ := hU V U
    exact (hq (f ≫ g) ⟨(PEL.Iso.PolarizedActionIso.pullbackComp U.data g.left f.left).symm.trans
      ((eg.pullback f.left).trans ef)⟩).trans
      (hq (𝟙 V) ⟨PEL.Iso.PolarizedActionIso.pullbackId U.data⟩).symm
  have hgf : g ≫ f = 𝟙 W := by
    obtain ⟨q, _, hq⟩ := hA W A
    exact (hq (g ≫ f) ⟨(PEL.Iso.PolarizedActionIso.pullbackComp A.data f.left g.left).symm.trans
      ((ef.pullback g.left).trans eg)⟩).trans
      (hq (𝟙 W) ⟨PEL.Iso.PolarizedActionIso.pullbackId A.data⟩).symm
  exact ⟨⟨f, g, hfg, hgf⟩, ⟨ef⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
