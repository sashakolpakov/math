import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Levels
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobenius

/-! # Frobenius Morphism -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusMorphism.BigPolynomialFrobeniusMorphism

noncomputable section

/-! # The actual polynomial Frobenius lift as a morphism of big crystalline objects -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "B" => MvPolynomial σ k
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "X₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X₀
local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p (Fact.out : p.Prime) B
  (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.prime_zero p k B)
local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "e" => WittVector.frobeniusEquiv p k

abbrev nativeLevel (n : ℕ) := FramedPolynomial.Levels.FramedPolynomialLevels.base p k B σ r hr hb n

def level (n : ℕ) : BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W B I γ bX :=
  (BigCrystalline.IntrinsicLifts.BigCrystallineIntrinsicLifts.inclusion p k B).obj (nativeLevel p k σ n)

def transformed : BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W B I γ bX ⥤
    BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W B I γ bX :=
  NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e (NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittFrobeniusDP p k).isDPMorphism
      (BigCrystalline.AffineFrobeniusComparison.BigCrystallineAffineFrobeniusComparison.over_base p k B) ⋙
    NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose g rfl

def ringMap (n : ℕ) : DividedPowers.DPMorphism (level p k σ n).dividedPowers
    ((transformed p k σ).obj (level p k σ n)).dividedPowers :=
  DividedPowers.DPMorphism.mk' (WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.levelMap_isDPMorphism p k σ n)

def quotientMap (n : ℕ) :=
  NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.quotientMap ((transformed p k σ).obj (level p k σ n))
    (level p k σ n) (BigPolynomialFrobeniusMorphism.ringMap p k σ n)

theorem quotient_residual (n : ℕ) :
    (quotientMap p k σ n).comp (NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv (nativeLevel p k σ n)).symm.toRingHom =
      (NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv (nativeLevel p k σ n)).symm.toRingHom.comp φ := by
  apply RingHom.ext
  intro b
  obtain ⟨x, rfl⟩ := (nativeLevel p k σ n).thickening.reduction_surjective b
  let A := (nativeLevel p k σ n).thickening.ring
  let ρ : A →+* B := (nativeLevel p k σ n).thickening.reduction
  let ψ : A →+* A := WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.levelMap p k σ n
  let q : A ⧸ RingHom.ker ρ →+* A ⧸ RingHom.ker ρ := quotientMap p k σ n
  let ε : A ⧸ RingHom.ker ρ ≃+* B := NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv (nativeLevel p k σ n)
  change q (ε.symm (ρ x)) = ε.symm (frobenius B p (ρ x))
  have hx : ε.symm (ρ x) = Ideal.Quotient.mk (RingHom.ker ρ) x :=
    RingHom.quotientKerEquivOfSurjective_symm_apply
      (nativeLevel p k σ n).thickening.reduction_surjective x
  have hy : ε.symm (ρ (ψ x)) = Ideal.Quotient.mk (RingHom.ker ρ) (ψ x) :=
    RingHom.quotientKerEquivOfSurjective_symm_apply
      (nativeLevel p k σ n).thickening.reduction_surjective (ψ x)
  have hψ : ρ (ψ x) = frobenius B p (ρ x) :=
    WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.levelMap_reduction p k σ n x
  have hq : q (Ideal.Quotient.mk (RingHom.ker ρ) x) =
      Ideal.Quotient.mk (RingHom.ker ρ) (ψ x) := rfl
  exact (congrArg q hx).trans (hq.trans (hy.symm.trans (congrArg ε.symm hψ)))

def morphism (n : ℕ) : (transformed p k σ).obj (level p k σ n) ⟶ level p k σ n where
  ringMap := BigPolynomialFrobeniusMorphism.ringMap p k σ n
  overBase := RingHom.ext (WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.levelMap_base p k σ n)
  overX := by
    let A := (nativeLevel p k σ n).thickening.ring ⧸
      RingHom.ker (nativeLevel p k σ n).thickening.reduction
    let q : CommRingCat.of A ⟶ CommRingCat.of A := CommRingCat.ofHom (quotientMap p k σ n)
    let s : CommRingCat.of B ⟶ CommRingCat.of A :=
      CommRingCat.ofHom (NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv (nativeLevel p k σ n)).symm.toRingHom
    let t : CommRingCat.of B ⟶ CommRingCat.of B := CommRingCat.ofHom φ
    have hc : s ≫ q = t ≫ s := by
      apply CommRingCat.hom_ext
      exact quotient_residual p k σ n
    have hs : Spec.map q ≫ Spec.map s = Spec.map s ≫ Spec.map t :=
      (Spec.map_comp s q).symm.trans ((congrArg Spec.map hc).trans (Spec.map_comp t s))
    change Spec.map q ≫ (Spec.map s ≫ 𝟙 (Spec (CommRingCat.of B))) =
      (Spec.map s ≫ 𝟙 (Spec (CommRingCat.of B))) ≫ Spec.map t
    simpa only [Category.comp_id] using hs

theorem ambient (n : ℕ) (x : (level p k σ n).ring) :
    (morphism p k σ n).ringMap x = WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.levelMap p k σ n x := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusMorphism.BigPolynomialFrobeniusMorphism
