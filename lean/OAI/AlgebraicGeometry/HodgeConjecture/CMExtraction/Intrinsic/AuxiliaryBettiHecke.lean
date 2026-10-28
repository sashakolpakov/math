import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryHecke
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass

/-! # Auxiliary Betti Hecke -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryBettiHecke

noncomputable section

/-! Actual spherical Hecke intertwining passes through any native Betti
class map and any of the constructed auxiliary radial embeddings. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [DecidableEq (Fin s)] [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry)

theorem native_auxiliary_theta_class_hecke
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (eH : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hBetti : ∀ (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (f : D.sphericalInputs),
      D.activeH1Complex A eH T
        (ThetaClass.nativeThetaClass D hg Θ f) = ThetaClass.nativeThetaClass D hg Θ (D.sphericalWeilComplex T f))
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
    (hp : ∀ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q, D.weil.finite.project (D.splitting (g, 1)) =
      (D.weil.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (ActiveBlockMatrices.Local.activeBlockGL c D.pel.reference.distinguished (Contragredient.Local.contragredient ℚ_[q] g))) *
            D.weil.finite.project u)
    (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished))
    (J : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] D.sphericalInputs)
    (hJ : ∀ b, (J b).val = AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    ∀ (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q), ThetaClass.nativeThetaClass D hg Θ (J (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b)) =
      Spectrum.nativeActiveHeckeActionOver D ℂ A eH T
        (ThetaClass.nativeThetaClass D hg Θ (J b)) := by
  intro T b
  have hact := LinearMap.congr_fun
    (Spectrum.nativeActiveHeckeActionOver_complex D A eH) T
  rw [show Spectrum.nativeActiveHeckeActionOver D ℂ A
      eH T =
        D.activeH1Complex A eH T from hact,
    hBetti, AuxiliaryHecke.native_spherical_auxiliary_complex D c u hp φ J hJ hElementaryDivisors]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryBettiHecke
