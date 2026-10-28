import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.Spherical
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ReferenceFrame
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeThreshold

/-! # Prime Preparation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PrimePreparation.CM

noncomputable section

/-! One actual prime bound simultaneously makes the prescribed source
input spherical and every integral local frame of the reference lattice
standard. The bound precedes the choice of ordinary prime. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  (hAdelicTheta : Adelic.ThetaBall.CM.AdelicThetaInput) (inputs : RepresentationTheory.Theta.Adelic.Prerequisites.Inputs.{0, 0})
  (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
  (Λ : Submodule ℤ (Fin 3 → E)) (hfg : Λ.FG)
  (hfull : Submodule.span ℚ (Λ : Set (Fin 3 → E)) = ⊤)

include hAdelicTheta inputs hfg hfull in
theorem exists_bound :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime q N →
      (∀ (f : E →+* ℚ_[q]) (u : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q), u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q →
        FactorTheta.CM.action E L f (u, 1) φ = φ) ∧
      (∀ (τ : E →+* ℚ_[q]) (χ : NumberField.RingOfIntegers E →+* ℤ_[q]),
        (∀ a : NumberField.RingOfIntegers E, τ a = (χ a : ℚ_[q])) →
        Local.Lattice.CM.localLattice τ Λ = Local.Lattice.CM.standard (q := q)) :=
  PrimeBounds.CM.combine _ _ _
    (SourceAdelic.Spherical.CM.exists_bound E L hAdelicTheta inputs φ)
    (Local.Lattice.CM.exists_uniform_local_frame Λ hfg hfull)
    (fun _ _ ha hb => ⟨ha, hb⟩)

include hAdelicTheta inputs hfg hfull in
theorem exists_threshold :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], N < q →
      (∀ (f : E →+* ℚ_[q]) (u : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q), u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q →
        FactorTheta.CM.action E L f (u, 1) φ = φ) ∧
      (∀ (τ : E →+* ℚ_[q]) (χ : NumberField.RingOfIntegers E →+* ℤ_[q]),
        (∀ a : NumberField.RingOfIntegers E, τ a = (χ a : ℚ_[q])) →
        Local.Lattice.CM.localLattice τ Λ = Local.Lattice.CM.standard (q := q)) :=
  PrimeThreshold.CM.of_coprime _ (exists_bound E L hAdelicTheta inputs φ Λ hfg hfull)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PrimePreparation.CM
