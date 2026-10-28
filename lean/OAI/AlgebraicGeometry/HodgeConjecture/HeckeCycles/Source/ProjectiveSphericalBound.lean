import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectiveLevel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralScalar
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedOpenFactors
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceExclusion
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicIntegral
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeBounds

/-! # Projective Spherical Bound -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectiveSphericalBound

noncomputable section

/-! The original source input is fixed by integral active SL3 outside
one prime bound. Projective openness and local-ring perfectness replace
the full AdelicTheta smooth-extension input. -/

attribute [local instance 2000] Subgroup.toGroup Prod.instGroup
open scoped Classical _root_.NumberField
open Filter OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

namespace CM
set_option cleanup.letToHave false

private def restrictLeft {A B G : Type*} [Group A] [Group B] [Group G]
    (f : A × B →* G) : A →* G := f.comp (MonoidHom.inl A B)

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

def finiteLevel (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    OpenSubgroup (SourceFinite.Product.CM.FiniteGroup E
      (OppositeCoordinates.CM.coordinates E L.coordinates)) :=
  (Finite.ProjectiveOpen.CM.allLevel (WeilData.CM.weilData E places) φ).comap
    (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates)
    (ProjectiveLevel.CM.projection_continuous E L)

theorem projective_bound (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime q N →
      ∀ (f : E →+* ℚ_[q]) (g),
        g ∈ SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates)
          (QadicPlace.CM.place E f) →
        RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace
          (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
          (QadicPlace.CM.place E f) g ∈ finiteLevel E L φ :=
  Finite.PlaceExclusion.CM.exists_embedding_bound
    (QuadraticConjugation.CM.Field.RealField E) (algebraMap (QuadraticConjugation.CM.Field.RealField E) E) _
    (RestrictedOpenFactors.CM.cofinite
      (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (finiteLevel E L φ))

variable {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance projectiveAwayGroup : Group (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  Subgroup.toGroup (FactorTheta.CM.RationalWeilFactorization.Away E L f)
local instance projectiveAwayMonoid : Monoid (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (projectiveAwayGroup E L f).toMonoid
local instance projectiveAwayMulOneClass : MulOneClass (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (projectiveAwayGroup E L f).toMulOneClass
local instance projectiveSourceMulOneClass :
    MulOneClass (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (show Group (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f)
    from Prod.instGroup).toMulOneClass

theorem active_line (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (hgood : SplitIntegralLocal.CM.Good (QuadraticConjugation.CM.Field.RealField E)
      (QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (QadicPlace.CM.place E f))
    (hlevel : ∀ g ∈ SourceFinite.Product.CM.levels E
      (OppositeCoordinates.CM.coordinates E L.coordinates) (QadicPlace.CM.place E f),
      RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace
        (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
        (QadicPlace.CM.place E f) g ∈ finiteLevel E L φ)
    (u : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (hu : u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) :
    ∃ c : ℂˣ, FactorTheta.CM.action E L f (u, 1) φ = (c : ℂ) • φ := by
  apply (CMExtraction.Finite.ProjectiveLevel.TestTransport.finiteProjectiveStabilizer_mem (WeilData.CM.weilData E places) φ
    (FactorTheta.CM.RationalWeilFactorization.splitting E L f (u, 1))).mp
  rw [SplittingProjection.CM.projection]
  change IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1) ∈ finiteLevel E L φ
  have he : IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (u, 1) =
      RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace
        (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
        (QadicPlace.CM.place E f)
        ((QadicSpecialLinear.CM.equivalence E
          (OppositeCoordinates.CM.coordinates E L.coordinates) f).symm u) := by
    refine (IntrinsicActiveClosure.CM.Intrinsic.active E L f u).trans ?_
    exact (SourceFinite.Product.CM.equivalence_apply E
      (OppositeCoordinates.CM.coordinates E L.coordinates) f u 1).trans (mul_one _)
  exact (congrArg (fun g : SourceFinite.Product.CM.FiniteGroup E
    (OppositeCoordinates.CM.coordinates E L.coordinates) => g ∈ finiteLevel E L φ) he).mpr
      (hlevel _ (QadicIntegral.CM.inverse_integral E
        (OppositeCoordinates.CM.coordinates E L.coordinates) f hgood u hu))

theorem exists_bound (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime q N →
      ∀ (f : E →+* ℚ_[q]) (u : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q), u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q →
        FactorTheta.CM.action E L f (u, 1) φ = φ := by
  apply PrimeBounds.CM.combine _ _ _ (projective_bound E L φ)
    (QadicIntegral.CM.exists_good_bound E (OppositeCoordinates.CM.coordinates E L.coordinates))
  intro q _ hf hg f
  exact IntegralScalar.CM.fixed q
    (restrictLeft (FactorTheta.CM.action E L f)) φ
    (active_line E L f φ (hg f) (hf f))

end CM

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectiveSphericalBound
