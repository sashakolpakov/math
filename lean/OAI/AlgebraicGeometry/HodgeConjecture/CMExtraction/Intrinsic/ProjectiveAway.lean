import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPELMatrix
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.ChosenProjectiveDepth
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PELLevel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.UnitaryAwayDensity

/-! # Projective Away -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectiveAway

noncomputable section

/-! The actual native away principal level preserves the line of the
same retained test. The required depth is the one chosen before q. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.ChosenProjectiveDepth.TestTransport

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hμ : D.pel.reference.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

theorem native_principal_away_preserves_line
    (huS : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he))
    (hlevel : 0 < D.pel.level)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (hfg : D.pel.reference.lattice.FG)
    (hspan : Submodule.span ℚ (D.pel.reference.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤)
    (hφ : φ ≠ 0) (hsupport : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0)
    (N : ℕ) (hN : 0 < N)
    (hperiod : ∀ z ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'), ∀ x,
      φ.val (z + x) = φ.val x)
    (hdiv : PEL.ChosenProjectiveDepth.TestTransport.pelProjectiveDepth E D.pel.reference e D.weil φ hfg hspan hφ hsupport N hN hperiod ∣
      D.pel.level) :
    let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D)
    ∀ a ∈ PELLevel.nativePELLevel E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel,
      ∃ z : ℂˣ, D.weil.finite.action a.val φ = (z : ℂ) • φ := by
  dsimp only
  let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D)
  intro a ha
  obtain ⟨γ, hγ⟩ := a.property
  have heq : RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu γ = a := Subtype.ext hγ
  have hm := (PELLevel.nativePELLevel_rational E D hg hμ v hv e he c u hu
    (UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel γ).mp (heq.symm ▸ ha)
  change FilledPEL.ParameterChoices.nativeFilledPEL E D.pel hg γ ∈ D.pel.reference.adelicPrincipalLevel D.pel.level at hm
  have ht := PEL.ChosenProjectiveDepth.TestTransport.pelProjectiveDepth_scalar E D.pel.reference e D.weil φ hfg hspan hφ hsupport N hN hperiod
    D.pel.level hdiv (FilledPEL.ParameterChoices.nativeFilledPEL E D.pel hg γ) hm
    (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu γ)
    (AwayPELMatrix.nativeAwayPEL_matrix E D hg hq hμ v hv e he c u hu huS γ)
  rwa [hγ] at ht

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectiveAway
