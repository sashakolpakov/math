import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.PolynomialFrobeniusEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedPolynomial

/-! # Frobenius Identification -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusIdentification.BigPolynomialFrobeniusIdentification

noncomputable section

/-! # The original geometric crystalline Frobenius is the explicit completed polynomial operator -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B (MvPolynomial σ W) r hr hb
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Big.AffineComparison.BigAffineCrystallineComparison.complexIso p k B σ r hr hb
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusNaturality.BigCrystallineAffineFrobeniusNaturality.coefficients p k
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusNaturality.BigCrystallineAffineFrobeniusNaturality.complexMap p k B σ r

theorem comparison_square :
    (e).hom ≫ Big.AffineFrobenius.BigAffineCrystallineFrobenius.complexMap p k B σ r hr hb =
      F ≫ ((Q).mapHomologicalComplex (.up ℕ)).map (e).hom := by
  unfold Big.AffineFrobenius.BigAffineCrystallineFrobenius.complexMap
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem original :
    Big.AffineFrobenius.BigAffineCrystallineFrobenius.complexMap p k B σ r hr hb =
      LiftedPolynomial.LiftedPolynomialFrameFrobenius.complexMap p k σ := by
  apply (cancel_epi (e).hom).mp
  rw [comparison_square]
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective A₀ ((K).X j)).2 α
  apply ULift.ext
  apply ULift.ext
  apply PD.PDDeRham.ext p k B Tower
  intro n
  exact (PolynomialFrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.original_mk p k σ j n x).trans
    (WittPolynomial.PolynomialFrameFrobenius.WittPolynomialFrameFrobenius.eval_formMap p k σ j n
      (((e).hom.f j (Ext.mk₀ x)).down.down)).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusIdentification.BigPolynomialFrobeniusIdentification
