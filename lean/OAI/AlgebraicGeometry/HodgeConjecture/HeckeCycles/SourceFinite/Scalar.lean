import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FixedFrameAuxiliaryFamily
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarTraceFrame

/-! # Scalar -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Scalar.CM

noncomputable section

/-! The source's own frame and multiplicity coefficient supply the
finite radial family. No coordinate basis or scalar eigenrelation is
assumed, and the complete native Galois splitting is retained. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places) Ga MpR MpF MpA)
  (hb : D.pel.reference.b = B.b)

include hb in
omit [IsGalois ℚ E] in
theorem matrix_eq : CMExtraction.Intrinsic.Multiplicity.nativeMatrix E D.pel.reference = Source.ScalarTraceFrame.CM.matrix E B := by
  unfold CMExtraction.Intrinsic.Multiplicity.nativeMatrix Source.ScalarTraceFrame.CM.matrix
  rw [hb]

include hb in
theorem exists_inputs
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) :
    ∃ u : MpF,
      FixedFrameAuxiliaryFamily.CM.Family.CoordinateIdentity E D (Source.ComplexAction.CM.Symplectic.frame E C) u ∧
      ∀ φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), φ ≠ 0 →
      ∃ (r : Eˣ) (M : ℕ), 0 < M ∧
      ∃ hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1,
        (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
          (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
            if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
        ∃ (Uq : Module.End ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q)) (ξ : ℂ),
          Function.Injective (CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ) ∧
          RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ξ ∧
          (∀ (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (x : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q), (Uq b).val x =
            (Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) : ℂ) *
              b.val (fun i => ((q : ℚ_[q]) ^ M)⁻¹ * x i)) ∧
          (∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
            D.weil.finiteAction (Source.NormOneScalar.CM.scalar E C r hr)
                (CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b) =
              ξ • CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ (Uq b)) := by
  have he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (Source.ComplexAction.CM.Symplectic.frame E C x)
      (Source.ComplexAction.CM.Symplectic.frame E C y) =
        RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm E (C.delta * C.a) (CMExtraction.Intrinsic.Multiplicity.nativeMatrix E D.pel.reference) x y := by
    intro x y
    rw [matrix_eq E D hb]
    exact Source.ScalarTraceFrame.CM.coordinates E C x y
  obtain ⟨u, hu, hfamily⟩ := FixedFrameAuxiliaryFamily.CM.Family.exists_family E D hLocalWeil hg hq ιE
    (C.delta * C.a) (Source.ScalarTraceFrame.CM.coefficient_ne_zero E C)
    (Source.ScalarTraceFrame.CM.coefficient_imaginary E C) (Source.ComplexAction.CM.Symplectic.frame E C) he
  refine ⟨u, hu, ?_⟩
  intro φ hφ
  obtain ⟨r, M, γ, Uq, ξ, hM, hr, hγ, hval, hJ, hξ, hUq, hf⟩ := hfamily φ hφ
  have hγ' : γ = Source.NormOneScalar.CM.scalar E C r hr :=
    Subtype.ext (hγ.trans (Source.NormOneScalar.CM.matrix_eq E C r hr).symm)
  subst γ
  exact ⟨r, M, hM, hr, hval, Uq, ξ, hJ, hξ, hUq, hf⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Scalar.CM
