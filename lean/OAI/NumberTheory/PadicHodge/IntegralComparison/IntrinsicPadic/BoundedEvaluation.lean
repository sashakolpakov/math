import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FreeEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IncomingChartObject
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.EvaluationObjectIso

/-! # Bounded Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BoundedEvaluation.Intrinsic

noncomputable section

/-! The actual global comparison is a section quasi-isomorphism at every
bounded object admitting a map to one of the genuine covering frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "JT" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "m" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n J

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

variable (V : BoundedCrystalline.Site.Objects (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n)

abbrev evaluationFunctor := Sheaf.EvaluationObjectIso.evaluationFunctor.{1,0,1,1} Rcoeff JT V

theorem quasiIso (i : GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
    (α : V ⟶ GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp (U i).val (U i).property n) :
    QuasiIso (((evaluationFunctor p Y n V).mapHomologicalComplex (.up ℕ)).map m) := by
  let C₀ := GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f (U i).val
  let : Algebra (ZMod p) C₀ := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ (U i).val)
  let g := GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp (U i).val (U i).property
  let hg := GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp (U i).val (U i).property
  let F₀ := GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp (U i).val (U i).property n
  let V₀ := Bounded.IncomingChartObject.object g hg n F₀ V α
  let e := Bounded.IncomingChartObject.iso g hg n F₀ V α
  have hv : QuasiIso (((evaluationFunctor p Y n
      ((BoundedOpen.Equivalence.postcompose g hg n).obj V₀)).mapHomologicalComplex (.up ℕ)).map m) :=
    FreeEvaluation.Intrinsic.globalMap_quasiIso p X Y f hp n (U i) J V₀ i le_rfl
  let := hv
  exact Sheaf.EvaluationObjectIso.quasiIso Rcoeff JT e m

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BoundedEvaluation.Intrinsic
