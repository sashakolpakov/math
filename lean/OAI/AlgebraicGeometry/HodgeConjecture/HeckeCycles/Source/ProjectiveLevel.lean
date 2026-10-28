import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ProjectiveOpen
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MarkedAwayLevel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SplittingProjection

/-! # Projective Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectiveLevel.CM

noncomputable section

/-! The original source test determines an open PEL level preserving
its line under the original source action. Only the proved symplectic
projection is needed; there is no new smooth-action agreement premise. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

theorem projection_continuous : Continuous (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun a => (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates a).val i j)
  have h := (continuous_apply i).comp
    (SourceFinite.ProjectionTopology.CM.original_action E L.coordinates (Pi.single j 1))
  simpa only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Function.comp_def, Matrix.col, Matrix.transpose_apply] using h

variable {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)

def projection : P.FiniteSpecialUnitary →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates).comp
    (PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb).symm.toMonoidHom

def level (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) : OpenSubgroup P.FiniteSpecialUnitary :=
  (Finite.ProjectiveOpen.CM.allLevel (WeilData.CM.weilData E places) φ).comap
    (projection E L P hb)
    ((projection_continuous E L).comp
      (PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb).symm.continuous)

variable {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

theorem product_line (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f)
    (ha : PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb
      (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f a) ∈ level E L P hb φ) :
    ∃ c : ℂˣ, FactorTheta.CM.action E L f a φ = (c : ℂ) • φ := by
  let g := IntrinsicActiveClosure.CM.Intrinsic.assemble E L f a
  let e := PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb
  let D := WeilData.CM.weilData E places
  have hm : ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates (e.symm (e g)) ∈
      CMExtraction.Finite.ProjectiveLevel.TestTransport.finiteProjectiveStabilizer D φ := ha
  have hg : ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates g ∈
      CMExtraction.Finite.ProjectiveLevel.TestTransport.finiteProjectiveStabilizer D φ :=
    (congrArg (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates) (e.symm_apply_apply g)) ▸ hm
  have hp : D.finite.project (FactorTheta.CM.RationalWeilFactorization.splitting E L f a) =
      ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates g :=
    SplittingProjection.CM.projection E L f a.1 a.2
  exact (CMExtraction.Finite.ProjectiveLevel.TestTransport.finiteProjectiveStabilizer_mem D φ (FactorTheta.CM.RationalWeilFactorization.splitting E L f a)).mp (hp.symm ▸ hg)

theorem away_line {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ P.lattice]
    (b : Module.Basis J ℤ P.lattice) (N : ℕ) (hN : 0 < N)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (hK : P.adelicPrincipalLevel N ≤ (level E L P hb φ).toSubgroup)
    (a : FactorTheta.CM.RationalWeilFactorization.Away E L f) (ha : a ∈ MarkedAwayLevel.CM.level E L P hb f b N hN) :
    ∃ c : ℂˣ, FactorTheta.CM.action E L f (1, a) φ = (c : ℂ) • φ := by
  apply product_line E L P hb f φ (1, a)
  exact Eq.mpr (congrArg
    (fun g : SourceFinite.Product.CM.FiniteGroup E
        (OppositeCoordinates.CM.coordinates E L.coordinates) =>
      PELFiniteGroup.CM.pel E
        (OppositeCoordinates.CM.coordinates E L.coordinates) P hb g ∈ level E L P hb φ)
    (MarkedAwayLevel.CM.assemble_away E L f a)) (hK ha)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectiveLevel.CM
