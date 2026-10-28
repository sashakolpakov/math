import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.RealPeriodChanges
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallReflectionLifts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.FiberBallPoint
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying

/-! # Ball Coordinate Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData

noncomputable section

/-! The actual native Hermitian form of an original PEL object has
normalized ball coordinates. Selected-place unitary changes preserve
its original Chern form and commute with its integral action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K} {κ : K →+* ℂ}
    (A : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)

local notation "PA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian PA
local notation "LA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.polarizationLineBundle A.polarized
local notation "hLA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.polarizationLineBundle_ample A.polarized

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects.PELObject.original_distinguished_lieRank [IsGalois ℚ E]
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ) :
    LieRanks.HasLieRank A.polarized.abelian A.action
      (P.μ.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2 := by
  have hr := A.complexFiber_distinguished_rank κ hκ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) (Category.id_comp _) hP
  exact LieTransport.hasLieRank_transport (A.action.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) A.action
    A.polarized.abelian.pullbackIdIso (PEL.Objects.PELIso.pullbackId A).action _ 2 hr

structure NativeBallCoordinateData where
  normalizer : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec
  hermitian : ∀ x y, Datum.RankThreePELDatum.complexMatrixHermitian P.μ
    (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A.polarized A.action s hs rfl hdegree A.rosati P.normalizedImaginaryScalar)
    (normalizer x) (normalizer y) =
      Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y
  point : P.Domain
  hodgeLine : Normalized.HodgeLine.NativeHermitianMarking.nativeNormalizedHodgeLine A.polarized A.action s hs rfl hdegree
    (P.embeddings P.distinguished) normalizer = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector point.val}

def nativeBallCoordinateData [IsGalois ℚ E]
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ) : NativeBallCoordinateData A hs hdegree := by
  apply Classical.choice
  obtain ⟨hξ, hc, hi⟩ := Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP
  have hr := A.original_distinguished_lieRank hP hκ
  obtain ⟨e, he⟩ := HermitianNormalizer.IntrinsicHermitianMarking.exists_nativeHermitian_normalizer A.polarized A.action s hs rfl hdegree
    (P.embeddings P.distinguished) A.rosati P.normalizedImaginaryScalar hξ hc hi hr
    P.b hP.2.1 hP.2.2.2.1
  obtain ⟨z, ⟨hz, hnegative⟩, _⟩ := Normalized.HodgeLine.NativeHermitianMarking.exists_unique_nativeHodge_ball_coordinate
    A.polarized A.action s hs rfl hdegree (P.embeddings P.distinguished) e A.rosati
    P.normalizedImaginaryScalar hξ hc hi P.b he hr
  exact ⟨⟨e, he, ⟨z, (Datum.RankThreePELDatum.mem_domain_iff_diagonal z).mpr hnegative⟩, hz⟩⟩

namespace NativeBallCoordinateData

variable {A hs hdegree} (D : NativeBallCoordinateData A hs hdegree)

def components (r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (i : Fin s) : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec :=
  if i = P.distinguished then D.normalizer.symm.trans (r.trans D.normalizer)
  else LinearEquiv.refl ℂ Geometry.ComplexBall.PrescribedSignsB.Vec

theorem components_distinguished (r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    D.components r P.distinguished (D.normalizer v) = D.normalizer (r v) := by
  simp only [NativeBallCoordinateData.components, ↓reduceIte, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem components_isometry (r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hr : ∀ x y, Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) (r x) (r y) =
      Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) x y) (i : Fin s) (x y : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Datum.RankThreePELDatum.complexMatrixHermitian (P.embeddings i).toRingHom
      (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A.polarized A.action s hs rfl hdegree A.rosati P.normalizedImaginaryScalar)
      (D.components r i x) (D.components r i y) =
    Datum.RankThreePELDatum.complexMatrixHermitian (P.embeddings i).toRingHom
      (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A.polarized A.action s hs rfl hdegree A.rosati P.normalizedImaginaryScalar) x y := by
  by_cases hi : i = P.distinguished
  · subst i
    have he (v w : Geometry.ComplexBall.PrescribedSignsB.Vec) := (D.hermitian v w).trans (Normalized.HodgeLine.complexMatrixHermitian_diagonal P.μ P.b v w)
    simp only [NativeBallCoordinateData.components, ↓reduceIte, LinearEquiv.trans_apply]
    change Datum.RankThreePELDatum.complexMatrixHermitian P.μ _
      (D.normalizer (r (D.normalizer.symm x))) (D.normalizer (r (D.normalizer.symm y))) = _
    rw [he, hr]
    have hback := he (D.normalizer.symm x) (D.normalizer.symm y)
    rw [D.normalizer.apply_symm_apply, D.normalizer.apply_symm_apply] at hback
    exact hback.symm
  · simp only [NativeBallCoordinateData.components, ite_eq_right hi, LinearEquiv.refl_apply]

variable (hP : P.IsAdmissible)

def realChange (r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A₀ ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A₀ :=
  PEL.RealPeriodChanges.IntrinsicPELRealChanges.changeMap A.polarized A.action s hs rfl hdegree
    P.embeddings hP.1 (D.components r)

attribute [local irreducible] PEL.RealPeriodChanges.IntrinsicPELRealChanges.changeMap

theorem realChange_commutes (r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (a : NumberField.RingOfIntegers E)
    (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A₀) :
    D.realChange hP r (IntegralAction.IntrinsicIntegralAction.linearAction A.polarized.abelian PA A.action a v) =
      IntegralAction.IntrinsicIntegralAction.linearAction A.polarized.abelian PA A.action a (D.realChange hP r v) := by
  dsimp only [NativeBallCoordinateData.realChange, Module.End]
  exact PEL.RealPeriodChanges.IntrinsicPELRealChanges.changeMap_commutes A.polarized A.action s hs rfl hdegree
    P.embeddings hP.1 (D.components r) a v

theorem realChange_riemann (r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hr : ∀ x y, Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) (r x) (r y) =
      Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) x y)
    (v w : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A₀) :
    (RiemannForm.nativeRiemannForm A₀ LA hLA (D.realChange hP r v) (D.realChange hP r w)).im =
      (RiemannForm.nativeRiemannForm A₀ LA hLA v w).im :=
  PEL.RealPeriodChanges.IntrinsicPELRealChanges.changeMap_riemann A.polarized A.action s hs rfl hdegree
    P.embeddings hP.1 A.rosati P.normalizedImaginaryScalar
    (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1 (D.components r)
    (D.components_isometry r hr) v w

end NativeBallCoordinateData

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData
