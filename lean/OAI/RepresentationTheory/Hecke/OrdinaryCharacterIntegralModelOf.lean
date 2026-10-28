import OAI.RepresentationTheory.Hecke.IntegralModel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Models

/-! # Ordinary Character Integral Model Of -/

namespace OAI.RepresentationTheory.Hecke.OrdinaryCharacterIntegralModelOf.OrdinaryIntrinsic

noncomputable section

/-! Choose IntegralModel's complete geometric output once. The TateComparison model below
uses that identical scheme, universal family, components, and inclusions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] [IsGalois ℚ E] [Field K] [NumberField K]
  {s N : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (iota : E →+* K) (κ : K →+* ℂ) (M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)

/-- A record of the witnesses and all clauses returned by full IntegralModel. -/
structure IntegralModel where
  base : AlgebraicGeometry.PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ
  levelUnit : IsUnit (N : base.R)
  spread : AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N M.space M.universal base
  classifies : spread.IsReducedPELModuli P
  smooth : Smooth spread.toOver.hom
  proper : IsProper spread.toOver.hom
  projective : AlgebraicGeometry.PELModuli.IntegralModel.Components.RelativelyProjective spread.toOver
  count : ℕ
  components : AlgebraicGeometry.PELModuli.IntegralModel.Components.ComponentAlbaneseData spread.toOver count
  decomposition : (∐ components.S) ≅ spread.toOver
  geometry : ∀ j : Fin count,
    Smooth (components.S j).hom ∧ IsProper (components.S j).hom ∧
    AlgebraicGeometry.PELModuli.IntegralModel.Components.RelativelyProjective (components.S j) ∧ GeometricallyConnected (components.S j).hom ∧
    Smooth (components.A j).X.hom ∧ IsProper (components.A j).X.hom ∧
    GeometricallyConnected (components.A j).X.hom ∧
    components.IsComplexAlbanese base.complexPoint j
  betti : Function.Bijective (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
    (components.totalComplexMap base.complexPoint decomposition)).hom
  generation : ∀ j : Fin count, ∃ n : ℕ, 0 < n ∧
    ∀ t : AlgebraicGeometry.PELModuli.IntegralModel.Base.GeometricPoint base.base,
      Function.Surjective (components.sumOfDifferences j n t)

variable {P iota κ M}

theorem integralModel_nonempty (hIntegralModel : IntegralModel.OrdinaryCharacterIntrinsic.FullIntegralModelInput)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hP : P.IsAdmissible) (hEmb : κ.comp iota = P.μ)
    (hN : AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N) (hM : M.IsFine) :
    Nonempty (IntegralModel P iota κ M) := by
  obtain ⟨B, hunit, T, hclass, hsm, hpr, hproj, r, D, e, hgeom, hb, hgen⟩ :=
    hIntegralModel s hs hdegree P hP iota κ hEmb N hN M hM
  exact ⟨⟨B, hunit, T, hclass, hsm, hpr, hproj, r, D, e, hgeom, hb, hgen⟩⟩

def integralModelOfFullIntegralModel (hIntegralModel : IntegralModel.OrdinaryCharacterIntrinsic.FullIntegralModelInput)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hP : P.IsAdmissible) (hEmb : κ.comp iota = P.μ)
    (hN : AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N) (hM : M.IsFine) :
    IntegralModel P iota κ M :=
  Classical.choice (integralModel_nonempty hIntegralModel hs hdegree hP hEmb hN hM)

namespace IntegralModel

variable (I : IntegralModel P iota κ M) {q : ℕ} [Fact q.Prime]
  (C : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback I.base.generic).obj I.spread.toOver))
  (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])

abbrev heckeData : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E I.base.extension.carrier s q :=
  AlgebraicGeometry.HodgeConjecture.HeckeCycles.Models.CM.Hecke.data (P := P) (iota := iota) (κ := κ)
    (M := M.space) (U := M.universal) (B := I.base) (q := q)
    I.spread I.components I.decomposition C χ

omit [IsGalois ℚ E] in
/-- Full IntegralModel geometry is transported by proved PEL-family comparisons,
including classification on every reduced test scheme. -/
theorem heckeData_geometry (hP : P.IsAdmissible) (hEmb : κ.comp iota = P.μ)
    (hN : AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N) : (I.heckeData C χ).HasIntegralModelGeometry :=
  AlgebraicGeometry.HodgeConjecture.HeckeCycles.Models.CM.Hecke.geometry_from_integral (P := P) (iota := iota) (κ := κ)
    (M := M.space) (U := M.universal) (B := I.base) (q := q)
    I.spread I.components I.decomposition C χ
    hP hEmb hN.1 I.levelUnit I.classifies I.smooth I.proper I.projective
    I.geometry I.betti I.generation

end IntegralModel

end

end OAI.RepresentationTheory.Hecke.OrdinaryCharacterIntegralModelOf.OrdinaryIntrinsic
