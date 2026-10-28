import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SchrodingerReindex
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.TestReindex
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReindexMeasure

/-! # Weil Reindex Covers -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers.CM

/-! The real, finite, and adelic covers on a relabeled source coordinate space. -/

open scoped Classical
open _root_.MeasureTheory
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : I ≃ J) {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData J MpR MpF MpA)

omit [DecidableEq I] [DecidableEq J] in
theorem real_pairing (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) :
    (∫ y, (Real.TestReindex.CM.tests e f).val y * star ((Real.TestReindex.CM.tests e h).val y)) =
      ∫ x, f.val x * star (h.val x) :=
  Real.TestReindex.CM.integral_reindex e.symm (fun x => f.val x * star (h.val x))

omit [DecidableEq I] [DecidableEq J] in
theorem finite_pairing (μ : Measure (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    (∫ y, (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e f).val y *
      star ((Finite.ReindexHeisenberg.CM.Pairing.testEquiv e h).val y) ∂μ) =
      ∫ x, f.val x * star (h.val x) ∂ ReindexMeasure.CM.finiteMeasure e μ :=
  (ReindexMeasure.CM.finite_integral e μ (fun x => f.val x * star (h.val x))).symm

omit [DecidableEq I] [DecidableEq J] in
theorem adelic_pairing (μ : Measure (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) [SFinite μ] (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :
    (∫ y, (Adelic.TestReindex.CM.tests e f).val y *
      star ((Adelic.TestReindex.CM.tests e h).val y) ∂ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ) =
      ∫ x, f.val x * star (h.val x) ∂ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (ReindexMeasure.CM.finiteMeasure e μ) :=
  (ReindexMeasure.CM.adelic_integral e μ (fun x => f.val x * star (h.val x))).symm

def real : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) MpR :=
  SchrodingerReindex.CM.cover e (Real.TestReindex.CM.tests e)
    (Real.TestReindex.CM.tests_apply e) (Real.TestReindex.CM.tests_symm_apply e)
    (real_pairing e) W.real

def finite : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf W.finiteCharacter (ReindexMeasure.CM.finiteMeasure e W.finiteMeasure)
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) MpF :=
  SchrodingerReindex.CM.cover e (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e)
    (fun _ _ => rfl) (fun _ _ => rfl) (finite_pairing e W.finiteMeasure) W.finite

def adelic : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ W.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (ReindexMeasure.CM.finiteMeasure e W.finiteMeasure))
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) MpA := by
  letI := W.finiteMeasure_haar
  exact SchrodingerReindex.CM.cover e (Adelic.TestReindex.CM.tests e)
    (Adelic.TestReindex.CM.tests_apply e) (Adelic.TestReindex.CM.tests_symm_apply e)
    (adelic_pairing e W.finiteMeasure) W.adelic

theorem real_action (m : MpR) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) :
    (CM.real e W).action m f = (Real.TestReindex.CM.tests e).symm
      (W.real.action m (Real.TestReindex.CM.tests e f)) := rfl

theorem finite_action (m : MpF) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    (CM.finite e W).action m f = (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e).symm
      (W.finite.action m (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e f)) := rfl

theorem adelic_action (m : MpA) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :
    (CM.adelic e W).action m f = (Adelic.TestReindex.CM.tests e).symm
      (W.adelic.action m (Adelic.TestReindex.CM.tests e f)) := rfl

theorem real_projection (m : MpR) : (CM.real e W).project m = RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm (W.real.project m) := rfl

theorem finite_projection (m : MpF) : (CM.finite e W).project m = RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm (W.finite.project m) := rfl

theorem adelic_projection (m : MpA) : (CM.adelic e W).project m = RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm (W.adelic.project m) := rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers.CM.Product

/-! Coordinate transport preserves the exact real/finite central product. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers.CM
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : I ≃ J) {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData J MpR MpF MpA)

theorem factorization (r : MpR) (f : MpF) (h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    (CM.adelic e W).action (W.includeReal r * W.includeFinite f) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor h φ) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor ((CM.real e W).action r h) ((CM.finite e W).action f φ) := by
  apply (Adelic.TestReindex.CM.tests e).injective
  rw [adelic_action, LinearEquiv.apply_symm_apply, Adelic.TestReindex.CM.tests_tensor,
    W.factorization, Adelic.TestReindex.CM.tests_tensor, real_action, finite_action,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem includeReal_covers (r : MpR) :
    ((CM.adelic e W).project (W.includeReal r)).val = fun i j =>
      (((CM.real e W).project r).val i j, (1 : Matrix (Sum I I) (Sum I I) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) i j) := by
  rw [adelic_projection, real_projection]
  have h := W.includeReal_covers r
  apply Matrix.ext
  intro i j
  change (W.adelic.project (W.includeReal r)).val ((e.sumCongr e) i) ((e.sumCongr e) j) = _
  rw [h]
  apply Prod.ext
  · rfl
  · exact congrFun (congrFun (Matrix.reindexRingEquiv RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (e.sumCongr e).symm).map_one i) j

theorem includeFinite_covers (f : MpF) :
    ((CM.adelic e W).project (W.includeFinite f)).val = fun i j =>
      ((1 : Matrix (Sum I I) (Sum I I) ℝ) i j, ((CM.finite e W).project f).val i j) := by
  rw [adelic_projection, finite_projection]
  have h := W.includeFinite_covers f
  apply Matrix.ext
  intro i j
  change (W.adelic.project (W.includeFinite f)).val ((e.sumCongr e) i) ((e.sumCongr e) j) = _
  rw [h]
  apply Prod.ext
  · exact congrFun (congrFun (Matrix.reindexRingEquiv ℝ (e.sumCongr e).symm).map_one i) j
  · rfl

theorem decompose (a : MpA) (r : MpR)
    (h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ((CM.adelic e W).project a) = (CM.real e W).project r) :
    ∃ f : MpF, W.includeReal r * W.includeFinite f = a := by
  apply W.decompose a r
  apply SchrodingerReindex.CM.symplectic_injective e.symm
  rw [RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_map]
  exact h

def rationalSplit : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ →* MpA := W.rationalSplit.comp (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e)

theorem rationalSplit_covers (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) :
    (CM.adelic e W).project (Product.rationalSplit e W γ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) γ := by
  rw [adelic_projection]
  change RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm (W.adelic.project (W.rationalSplit (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e γ))) = _
  rw [W.rationalSplit_covers, RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_map, RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_symm_apply]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers.CM.Product

end

end OAI
