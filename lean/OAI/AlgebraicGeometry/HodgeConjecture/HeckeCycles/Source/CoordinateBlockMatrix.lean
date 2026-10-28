import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FixedFrameRationalConjugation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.CoefficientTransport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction

/-! # Coordinate Block Matrix -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.CoordinateBlockMatrix.CM.RationalConjugation

/-! The original rational source matrix is exactly the matrix used in
the retained finite trace frame. Hence the actual source rational lift
has the computed simultaneous local blocks. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem matrix (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count) (hb : P.b = B.b)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    (ComplexAction.CM.Symplectic.symplectic E C (Rational.CoefficientTransport.CM.equivalence P.b B.b hb g)).val =
      CMExtraction.RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix E P (ComplexAction.CM.Symplectic.frame E C) g := by
  apply Matrix.mulVec_injective
  funext x
  obtain ⟨y, rfl⟩ := (ComplexAction.CM.Symplectic.frame E C).surjective x
  rw [ComplexAction.CM.Symplectic.symplectic_apply, CMExtraction.RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix_apply]
  apply congrArg (ComplexAction.CM.Symplectic.frame E C)
  change (Rational.CoefficientTransport.CM.equivalence P.b B.b hb g).val.val.mulVec y = g.val.val.mulVec y
  rw [Rational.CoefficientTransport.CM.matrix]

variable {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places) Ga MpR MpF MpA)
  (hb : D.pel.reference.b = B.b) {n : ℕ} (c : GeometricSource.CM.Positions E places ≃ Fin n)

theorem actual_lift_conjugation (u : MpF)
    (hu : FixedFrameAuxiliaryFamily.CM.Family.CoordinateIdentity E D (ComplexAction.CM.Symplectic.frame E C) u)
    (g : D.RationalSU) (m : MpF)
    (hm : D.weil.finite.project m = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
      (ComplexAction.CM.Symplectic.symplectic E C (Rational.CoefficientTransport.CM.equivalence D.pel.reference.b B.b hb g))) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (D.weil.finite.project (u * m * u⁻¹)) =
        CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c (FixedFrameRationalConjugation.CM.blocks E D g) :=
  FixedFrameRationalConjugation.CM.actual_lift_conjugation E D (ComplexAction.CM.Symplectic.frame E C) c u hu g
    (ComplexAction.CM.Symplectic.symplectic E C (Rational.CoefficientTransport.CM.equivalence D.pel.reference.b B.b hb g))
    (matrix E C D.pel.reference hb g) m hm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.CoordinateBlockMatrix.CM.RationalConjugation

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.CoordinateBlockMatrix.CM

/-! The constructed finite coordinate identity gives the exact
conjugating matrix for every rational element of the original source. -/

open scoped Classical _root_.Matrix _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places) Ga MpR MpF MpA)
  (hb : D.pel.reference.b = B.b) {n : ℕ} (c : GeometricSource.CM.Positions E places ≃ Fin n)

include hb in
theorem rational (u : MpF)
    (hu : FixedFrameAuxiliaryFamily.CM.Family.CoordinateIdentity E D (ComplexAction.CM.Symplectic.frame E C) u)
    (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) ℚ_[q])
    (hS : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    S * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) (ComplexAction.CM.Symplectic.symplectic E C g) * S⁻¹ =
      CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c (fun i => Matrix.SpecialLinearGroup.map
        (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (i, false)) g.val) := by
  let t := Rational.CoefficientTransport.CM.equivalence D.pel.reference.b B.b hb
  let g' := t.symm g
  have hg : t g' = g := t.apply_symm_apply g
  have hm : g'.val = g.val :=
    (Rational.CoefficientTransport.CM.matrix D.pel.reference.b B.b hb g').symm.trans
      (congrArg Subtype.val hg)
  let γ := ComplexAction.CM.Symplectic.symplectic E C (t g')
  have hγ : γ = ComplexAction.CM.Symplectic.symplectic E C g := congrArg (ComplexAction.CM.Symplectic.symplectic E C) hg
  have hl := FixedFrameRationalConjugation.CM.conjugation E D (ComplexAction.CM.Symplectic.frame E C) c u hu g' γ
    (RationalConjugation.matrix E C D.pel.reference hb g')
  have hp := RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finite_coordinate_conjugation_projection q D.weil S u hS γ
  have hb' : FixedFrameRationalConjugation.CM.blocks E D g' =
      fun i => Matrix.SpecialLinearGroup.map (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (i, false)) g.val :=
    funext (fun i => congrArg (Matrix.SpecialLinearGroup.map (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (i, false))) hm)
  exact (congrArg (fun z : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) ℚ =>
      S * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) z * S⁻¹) hγ).symm.trans
        (hp.symm.trans (hl.trans (congrArg (CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c) hb')))

include hb in
theorem exists_matrix (u : MpF)
    (hu : FixedFrameAuxiliaryFamily.CM.Family.CoordinateIdentity E D (ComplexAction.CM.Symplectic.frame E C) u) :
    ∃ S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) ℚ_[q],
      D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S ∧
      ∀ g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b,
        S * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) (ComplexAction.CM.Symplectic.symplectic E C g) * S⁻¹ =
          CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c (fun i => Matrix.SpecialLinearGroup.map
            (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (i, false)) g.val) := by
  obtain ⟨S, hS, hp⟩ := hu
  exact ⟨S, hS, rational E C D hb c u ⟨S, hS, hp⟩ S hS⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.CoordinateBlockMatrix.CM

end

end OAI
