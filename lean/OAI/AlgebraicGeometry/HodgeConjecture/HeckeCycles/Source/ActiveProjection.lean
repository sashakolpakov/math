import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveProjectionSupport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalBlockConjugation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalProductBlocks
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PrimeDetermination
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SingleBlockPhase

/-! # Active Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveProjection.CM

noncomputable section

/-! The actual original source active projection has exactly the
indexed symplectic matrix required by the radial Hecke action. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

theorem local_conjugation {I : Type*} [Fintype I] [DecidableEq I]
    (q : ℕ) [Fact q.Prime] (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ_[q]) (A : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S * A * (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S)⁻¹) =
      S * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom A * S⁻¹ := by
  simp only [map_mul, map_inv, RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion_projection]

theorem other_conjugation {I : Type*} [Fintype I] [DecidableEq I]
    (q p : ℕ) [Fact q.Prime] [Fact p.Prime] (hpq : p ≠ q)
    (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ_[q]) (A : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hA : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom A = 1) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom
      (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S * A * (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S)⁻¹) = 1 := by
  simp only [map_mul, map_inv, RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime.Realization.finitePadicSymplecticInclusion_other_prime q p hpq, hA,
    inv_one, one_mul]

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {q : ℕ} [Fact q.Prime]
  (τ : Fin places.count → E →+* ℚ_[q]) (μ : Fin places.count)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)
  {n : ℕ} (c : GeometricSource.CM.Positions E places ≃ Fin n) (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) ℚ_[q])

include hb in
theorem conjugation
    (hτ : ∀ i, i ≠ μ → QadicPlace.CM.place E (τ i) ≠ QadicPlace.CM.place E (τ μ))
    (hr : ∀ g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b,
      S * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) (ComplexAction.CM.Symplectic.symplectic E L.coordinates g) * S⁻¹ =
        CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c (fun i => Matrix.SpecialLinearGroup.map (τ i) g.val))
    (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S *
      ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
        (IntrinsicActiveClosure.CM.Intrinsic.assemble E L (τ μ) (a, 1)) *
          (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S)⁻¹ =
      RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic (CMExtraction.ActiveBlockMatrices.Local.activeBlockGL c μ (CMExtraction.Contragredient.Local.contragredient ℚ_[q] a))) := by
  let A := ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
    (IntrinsicActiveClosure.CM.Intrinsic.assemble E L (τ μ) (a, 1))
  have hq := (local_conjugation q S A).trans
    ((LocalBlockConjugation.CM.conjugation E L (τ μ) τ c S hr (a, 1)).trans
      (congrArg (CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c) (LocalProductBlocks.CM.active_blocks E L τ μ hτ a)))
  have ho : ∀ (p : ℕ) [Fact p.Prime], p ≠ q →
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom
        (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S * A * (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S)⁻¹) = 1 := by
    intro p hp hpq
    exact other_conjugation q p hpq S A
      (ActiveProjectionSupport.CM.other E L (τ μ) P hb a p hpq)
  exact (Finite.PrimeDetermination.CM.supported q _ _ hq ho).trans (SingleBlockPhase.CM.finite q c μ a)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveProjection.CM
