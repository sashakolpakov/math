import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedTermLimit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.TermEvaluation

/-! # Lifted Section Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedSectionEvaluation.CrystallineLiftedSectionEvaluation

noncomputable section

/-! # Original lifted section coordinates evaluated on native polynomial levels -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

private theorem inv_hom_apply {R : Type*} [Ring R] {M N : ModuleCat R}
    (e : M ≅ N) (x : N) : e.hom (e.inv x) = x :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e.inv_hom_id) x

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff) [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "Poly" => MvPolynomial σ W
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "Native" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "KS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafCech.CrystallineFrameSheafCech.sectionPresheafIso p k B σ a
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase

theorem coordinates (j : ℕ)
    (s : (Functor.const Nativeᵒᵖ).obj (ModuleCat.of R R) ⟶ ((KS).X j).obj)
    (Q : Nativeᵒᵖ) :
    (CrystallineFrame.TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase j).π.app Q
        (LiftedTermLimit.CrystallineLiftedTermLimit.sectionsEquiv p k B σ r hr hbase j s).down =
      ((e j).hom.app Q (s.app Q (1 : R))).down := by
  let z := LiftedTermLimit.CrystallineLiftedTermLimit.sectionsEquiv p k B σ r hr hbase j s
  let f := (CrystallineFrame.TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase j).π.app Q
  have hs := Module.ConeSections.ModuleConeSections.sectionsEquiv_eval R
    (LiftedTermLimit.CrystallineLiftedTermLimit.cone p k B σ r hr hbase j)
    (LiftedTermLimit.CrystallineLiftedTermLimit.isLimit p k B σ r hr hbase j) s Q
  have he := congrArg (fun x => (e j).hom.app Q x) hs
  change (e j).hom.app Q ((e j).inv.app Q ((E).map f z)) =
    (e j).hom.app Q (s.app Q (1 : R)) at he
  exact congrArg ULift.down ((inv_hom_apply ((e j).app Q) ((E).map f z)).symm.trans he)

theorem evaluation (j n : ℕ)
    (s : (Functor.const Nativeᵒᵖ).obj (ModuleCat.of R R) ⟶ ((KS).X j).obj) :
    CrystallineFrame.TermEvaluation.CrystallineFrameTermEvaluation.evaluation p k B σ r hr hbase n j
      (((e j).hom.app (op (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n))
        (s.app (op (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n)) (1 : R))).down) =
    TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k B Tower n).toLinearMap LinearMap.id
      (LiftedTermLimit.CrystallineLiftedTermLimit.sectionsEquiv p k B σ r hr hbase j s).down :=
  (congrArg (CrystallineFrame.TermEvaluation.CrystallineFrameTermEvaluation.evaluation p k B σ r hr hbase n j)
    (coordinates p k B σ r hr hbase j s
      (op (FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hbase n))).symm).trans
    (CrystallineFrame.TermEvaluation.CrystallineFrameTermEvaluation.projection p k B σ r hr hbase n j
      (LiftedTermLimit.CrystallineLiftedTermLimit.sectionsEquiv p k B σ r hr hbase j s).down)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedSectionEvaluation.CrystallineLiftedSectionEvaluation
