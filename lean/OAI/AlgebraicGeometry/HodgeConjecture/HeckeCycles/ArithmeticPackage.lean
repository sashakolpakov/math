import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Prime

/-! # Arithmetic Package -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticPackage.CM

noncomputable section

/-! Retain IntegralModel's full conclusion while applying CMPoints to the same family.
The native Hecke geometry, ordinary reduction and conjugate lattice frames
all refer to these one-time choices of integral models and Albanese schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticModels.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Models.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FramedOrdinary.CM.Ordinary
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Frames.CM

universe u v

theorem integral_ordinary_hecke_models
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    [NumberField.IsCMField E] (places : GeometricSource.CM.Places E)
    {K : Type} [Field K] [NumberField K]
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count)
    (iota : E →+* K) (κ : K →+* ℂ) (N : ℕ)
    (F : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
    (hs : 0 < places.count) (hdegree : Module.finrank ℚ E = 2 * places.count)
    (hP : P.IsAdmissible) (hEmb : κ.comp iota = P.μ)
    (hN : PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N)
    (hF : F.IsFine) (hball : F.HasProjectiveBallComponents κ)
    (hintegral : ArithmeticModels.CM.IntegralConclusion P iota κ N F)
    (h_CMPoints : Ordinary.Models.CM.CMPointsInput.{u,v})
    {ι : Type u} [Fintype ι] (L : ι → Type v)
    [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ)
      (V : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N F.space F.universal B)
      (r : ℕ) (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData V.toOver r) (e : (∐ D.S) ≅ V.toOver)
      (d : ℕ),
      let Q := Ordinary.Models.CM.singletonModel P iota κ N F B V r D e
      bound ≤ d ∧ Q.HasPrescribedBallPeriods ∧
      (∀ (q : ℕ) [Fact q.Prime]
        (C : AbelianScheme.TateComparison.Local.IntegralType places.count →
          AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback B.generic).obj V.toOver))
        (χ : Fin places.count × Bool → NumberField.RingOfIntegers E →+* ℤ_[q]),
        (Models.CM.Hecke.data V D e C χ).HasIntegralModelGeometry) ∧
      (∀ (q : ℕ) [Fact q.Prime], d < q → ∀ (j : Q.QadicChoice q)
        (v : Fin places.count × Bool),
        Local.Lattice.CM.localLattice (Local.Frames.CM.pairedEmbedding E j Q.extendedEmbedding places v)
          P.lattice = Local.Lattice.CM.standard (q := q)) ∧
      Ordinary.Models.CM.OrdinaryConclusion E K Q L excluded d := by
  obtain ⟨B, hunit, V, hclassifies, hsmooth, hproper, hprojective,
    r, D, e, hcomponents, hbetti, hgeneration⟩ := hintegral
  let Q := Ordinary.Models.CM.singletonModel P iota κ N F B V r D e
  have hQ : Q.HasPrescribedBallPeriods := by
    refine ⟨hs, hdegree, fun _ => ?_⟩
    exact ⟨hP, hEmb, hN, hF, hball, hclassifies, hsmooth, hproper, hprojective,
      fun j => ⟨(hcomponents j).1, (hcomponents j).2.1,
        (hcomponents j).2.2.1, (hcomponents j).2.2.2.1⟩⟩
  obtain ⟨d, hbound, hframes, hord⟩ :=
    FramedOrdinary.CM.Ordinary.ordinary_with_local_frames E K Q hQ (0 : Fin 1) places h_CMPoints L excluded bound
  refine ⟨B, V, r, D, e, d, hbound, hQ, ?_, hframes, hord⟩
  intro q _ C χ
  exact Models.CM.Hecke.geometry_from_integral V D e C χ hP hEmb hN.1 hunit
    hclassifies hsmooth hproper hprojective hcomponents hbetti hgeneration

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticPackage.CM
