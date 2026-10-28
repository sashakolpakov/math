import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PELLevel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.UnitaryAwayDensity
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PrincipalCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralLattice

/-! # Marked Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MarkedLevel

noncomputable section

/-! The concrete open native away level has exactly the original
marked lattice meaning, including every non-active integral local block. -/

open scoped Classical _root_.Matrix _root_.NumberField

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
  (hN : 0 < D.pel.level)

theorem nativePELLevel_marked (hq : D.pel.IsGoodCompletelySplitPrime)
    (hchar : ∀ w (a : NumberField.RingOfIntegers E), D.localEmbedding w a = D.pel.localCharacter w a)
    (hstandard : ∀ w, D.localReferenceLattice w = RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q))
    (γ : D.RationalSU) :
    let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D)
    RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu γ ∈
      PELLevel.nativePELLevel E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D) hN ↔
        γ ∈ D.rationalAwayLevel ∧ ∀ w : Fin s × Bool,
          w.1 ≠ D.pel.reference.distinguished → D.localMatrix w γ ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q := by
  let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D)
  let := AdmissibleAwayLevel.Approximation.admissible_lattice E D.pel.reference hg.reference_admissible
  let b := Module.Free.chooseBasis ℤ D.pel.reference.lattice
  have hP := PrincipalCoordinates.ParameterChoices.nativeFilledPEL_principal_iff E D.pel hg hq
    (IntegralLattice.ParameterChoices.native_local_lattices_standard D hchar hstandard) b D.pel.level hN hq.2.2.1 γ
  have ha : (Matrix.SpecialLinearGroup.toLin' γ.val).restrictScalars ℚ ∈
      AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup (LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.pel.reference.lattice q).toAddSubgroup D.pel.level ↔
        γ ∈ D.rationalAwayLevel := Iff.rfl
  have hm (w : Fin s × Bool) : D.localMatrix w γ =
      Matrix.SpecialLinearGroup.map (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel w) γ.val :=
    congrArg (fun σ : E →+* Padic q => Matrix.SpecialLinearGroup.map σ γ.val)
      (IntegralLattice.ParameterChoices.originalLocalEmbedding_eq_native D hchar w)
  have hl : (∀ w : Fin s × Bool, w.1 ≠ D.pel.reference.distinguished →
      Matrix.SpecialLinearGroup.map (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel w) γ.val ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) ↔
        ∀ w : Fin s × Bool, w.1 ≠ D.pel.reference.distinguished →
          D.localMatrix w γ ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q :=
    forall_congr' (fun w => imp_congr_right (fun _ => Iff.of_eq
      (congrArg (fun g => g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (hm w).symm)))
  exact (PELLevel.nativePELLevel_rational E D hg hμ v hv e he c u hu (UnitaryAwayDensity.nativeUnitaryActivePlace E D) hN γ).trans
    (hP.trans (and_congr ha hl))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MarkedLevel
