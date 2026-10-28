import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Moduli
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Definitions

/-! # Arithmetic Models -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticModels.CM

noncomputable section

/-! Obtain the actual integral PEL spread, component Albanese schemes,
total H1 comparison, and geometric-fiber generation from the named IntegralModel
prerequisite at the deep levels constructed by ReferenceFamily. -/

open scoped Classical
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Moduli.CM

def IntegralConclusion
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E] [Field K] [NumberField K]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (iota : E →+* K) (κ : K →+* ℂ)
    (N : ℕ) (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) : Prop :=
  ∃ B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ,
    IsUnit (N : B.R) ∧
    ∃ T : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B,
      PELModuli.IntegralModel.PEL.Has.IntegralPELSpread.IsReducedPELModuli P T ∧
      Smooth T.toOver.hom ∧ IsProper T.toOver.hom ∧ PELModuli.IntegralModel.Components.RelativelyProjective T.toOver ∧
      ∃ (r : ℕ) (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData T.toOver r) (e : (∐ D.S) ≅ T.toOver),
        (∀ j : Fin r,
          Smooth (D.S j).hom ∧ IsProper (D.S j).hom ∧ PELModuli.IntegralModel.Components.RelativelyProjective (D.S j) ∧
          GeometricallyConnected (D.S j).hom ∧
          Smooth (D.A j).X.hom ∧ IsProper (D.A j).X.hom ∧
          GeometricallyConnected (D.A j).X.hom ∧ D.IsComplexAlbanese B.complexPoint j) ∧
        Function.Bijective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
          (D.totalComplexMap B.complexPoint e)).hom ∧
        (∀ j : Fin r, ∃ n : ℕ, 0 < n ∧ ∀ t : PELModuli.IntegralModel.Base.GeometricPoint B.base,
          Function.Surjective (D.sumOfDifferences j n t))

/-- The full IntegralModel proposition, available only as an explicit named hypothesis. -/
def IntegralModelInput : Prop :=
  ∀ {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E] [Field K] [NumberField K]
    (s : ℕ) (_hs : 0 < s) (_hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (_hP : P.IsAdmissible)
    (iota : E →+* K) (κ : K →+* ℂ) (_h_embedding : κ.comp iota = P.μ)
    (N : ℕ) (_hN : PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (_hM : M.IsFine),
      IntegralConclusion P iota κ N M

/-- The ReferenceFamily torsion and determinant conclusions establish IntegralModel's full
level hypothesis; its integral and Albanese data are then obtained for
every positive multiple of the constructed depth. -/
theorem deep_integral_models
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E] [Field K] [NumberField K]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (iota : E →+* K) (κ : K →+* ℂ) (h_embedding : κ.comp iota = P.μ)
    (h_ReferenceFamily : Moduli.CM.ReferenceFamilyInput) (h_IntegralModel : IntegralModelInput)
    (Kaux : OpenSubgroup P.FiniteSpecialUnitary) (Mbase : ℕ) (hMbase : 0 < Mbase) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ Mbase ∣ N₀ ∧
      ∀ N : ℕ, 0 < N → N₀ ∣ N →
        P.adelicPrincipalLevel N ≤ Kaux.toSubgroup ∧
        PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N ∧
        ∃ S : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N,
          S.IsFine ∧ S.HasProjectiveBallComponents κ ∧
          (∃ (Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
            (C₀ : S.ComplexComponent κ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety),
            (∀ g, g ∈ Γ ↔ AbelianModuli.ReferenceFamily.Definitions.SpecialUnitaryPrincipalLevel P.b P.lattice N g) ∧
            S.IsProjectiveComponent κ C₀ X ∧ P.IsUniformizedBy X Γ) ∧
          IntegralConclusion P iota κ N S := by
  obtain ⟨N₀, hN₀, hbase, hlevels⟩ :=
    h_ReferenceFamily s hs hdegree P hP iota κ h_embedding Kaux Mbase hMbase
  refine ⟨N₀, hN₀, hbase, ?_⟩
  intro N hN hdiv
  obtain ⟨hdet, hadelic, Γ, hΓ, htor, S, hSfine, hSprojective, C₀, X, hX, hunif⟩ :=
    hlevels N hN hdiv
  have hdeep : PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N := by
    refine ⟨hN₀.trans (Nat.le_of_dvd hN hdiv), ?_⟩
    intro g hg k hk hpow
    exact htor g ((hΓ g).mpr ⟨hg, hdet g hg⟩) k hk hpow
  exact ⟨hadelic, hdeep, S, hSfine, hSprojective, ⟨Γ, C₀, X, hΓ, hX, hunif⟩,
    h_IntegralModel s hs hdegree P hP iota κ h_embedding N hdeep S hSfine⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticModels.CM
