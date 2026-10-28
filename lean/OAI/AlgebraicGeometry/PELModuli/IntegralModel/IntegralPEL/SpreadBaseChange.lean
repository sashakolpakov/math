import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericFamilyComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FineBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.TowerEmbedding

/-! # Spread Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Further arithmetic base change preserves the full reduced PEL
classifier and reconstructs the exact comparison with the supplied family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iota : E →+* K} {κ : K →+* ℂ} {B : Base.ArithmeticBaseExtension K κ}
    {M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N}
    (T : PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B)

theorem PEL.Has.IntegralPELSpread.action_classifies (hT : T.IsReducedPELModuli P)
    (Y : Over B.base) [IsReduced Y.left]
    (A : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N Y) :
    ∃! f : Y ⟶ T.toOver, Nonempty (PEL.Iso.PolarizedActionIso (T.universal.pullback f).data A.data) := by
  obtain ⟨f, ⟨a⟩, hu⟩ := hT Y A
  refine ⟨f, ⟨a.toActionIso.trans (PEL.Iso.PolarizedActionIso.pullbackId A.data)⟩, ?_⟩
  rintro g ⟨b⟩
  exact hu g ⟨PEL.Has.PulledBackPELDataIso.ofActionIso
    (b.trans (PEL.Iso.PolarizedActionIso.pullbackId A.data).symm)⟩

variable (D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding)
    (φ : B.R →+* D.R)
    (hφ : D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField)

def PEL.Has.IntegralPELSpread.baseChangeUniversal :
    PEL.Has.IntegralPELObject P (B.compose D).R ((B.compose D).integralEmbedding iota) N
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj T.toOver) :=
  (T.universal.baseChange φ).changeEmbedding (B.compose_integralEmbedding D φ hφ iota)

theorem PEL.Has.IntegralPELSpread.baseChangeUniversal_classifies (hT : T.IsReducedPELModuli P)
    (Y : Over (B.compose D).base) [IsReduced Y.left]
    (A : PEL.Has.IntegralPELObject P (B.compose D).R ((B.compose D).integralEmbedding iota) N Y) :
    ∃! f : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj T.toOver,
      Nonempty (PEL.Iso.PolarizedActionIso ((T.baseChangeUniversal D φ hφ).pullback f).data A.data) :=
  IntegralPEL.FineComparison.integralPEL_fine_changeEmbedding (T.universal.baseChange φ) (B.compose_integralEmbedding D φ hφ iota)
    (IntegralPEL.FineBaseChange.integralPEL_fine_baseChange T.universal (T.action_classifies hT) φ) Y A

variable [IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj T.toOver).left]

def PEL.Has.IntegralPELSpread.baseChangeFine (hT : T.IsReducedPELModuli P) (hM : M.IsFine) :
    PEL.Has.IntegralPELSpread P iota κ N M.space M.universal (B.compose D) :=
  Arithmetic.GenericFamilyComparison.integralPELSpreadOfFineModel (B.compose D) (T.baseChangeUniversal D φ hφ) M
    (T.baseChangeUniversal_classifies D φ hφ hT) hM

theorem PEL.Has.IntegralPELSpread.baseChangeFine_toOver (hT : T.IsReducedPELModuli P) (hM : M.IsFine) :
    (T.baseChangeFine D φ hφ hT hM).toOver =
      (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj T.toOver := rfl

theorem PEL.Has.IntegralPELSpread.baseChangeFine_isReducedPELModuli
    (hT : T.IsReducedPELModuli P) (hM : M.IsFine) :
    (T.baseChangeFine D φ hφ hT hM).IsReducedPELModuli P :=
  Arithmetic.GenericFamilyComparison.integralPELSpreadOfFineModel_isReducedPELModuli (B.compose D) (T.baseChangeUniversal D φ hφ) M
    (T.baseChangeUniversal_classifies D φ hφ hT) hM

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
