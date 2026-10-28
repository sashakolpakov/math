import OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicPDP
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Lifting

/-! # Padic Frames -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicFrames.PadicCrystallineFrames

noncomputable section

/-!
# Polynomial crystalline frames modulo powers of p

Every affine crystalline object maps to one of these frames on its own
affine open. The frames use p-power quotients and require only the actual
crystalline condition that p is nilpotent in the target.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
variable (B : Type u) [CommRing B] [Algebra k B]

local notation "W" => WittVector p k
local notation "A" => MvPolynomial B W
local notation "I₀" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP.EnvelopeThickening.polynomialReduction p k B
local notation "I" => RingHom.ker r
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope W A I₀ δ₀ I
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal W A I₀ δ₀ I
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers W A I₀ δ₀ I
local notation "rE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP.EnvelopeThickening.envelopeReduction p k B A r
  (EnvelopeThickeningP.EnvelopeThickening.polynomialReduction_surjective p k B)
  (EnvelopeThickeningP.EnvelopeThickening.polynomialReduction_base p k B)
local notation "hE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_kernel p k B A r
  (EnvelopeThickeningP.EnvelopeThickening.polynomialReduction_surjective p k B)
  (EnvelopeThickeningP.EnvelopeThickening.polynomialReduction_base p k B)

local instance envelopeBaseAlgebra : Algebra W E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ I).comp (algebraMap W A)).toAlgebra

def envelopeDP : DividedPowers (RingHom.ker rE) :=
  DividedPowers.ofRingEquiv (e := RingEquiv.refl E)
    (by
      change (J).map (RingHom.id E) = RingHom.ker rE
      rw [Ideal.map_id]
      exact (hE).symm) δ

theorem envelope_baseDP :
    DividedPowers.IsDPMorphism δ₀ (envelopeDP p k B) (algebraMap W E) where
  ideal_comp := by
    rw [hE]
    exact (PD.EnvelopeDp.PDEnvelope.base_isDPMorphism W A I₀ δ₀ I
      (EnvelopeThickeningP.EnvelopeThickening.baseIdeal_le_kernel p k B A r
        (EnvelopeThickeningP.EnvelopeThickening.polynomialReduction_base p k B))).ideal_comp
  dpow_comp x hx :=
    (PD.EnvelopeDp.PDEnvelope.base_isDPMorphism W A I₀ δ₀ I
      (EnvelopeThickeningP.EnvelopeThickening.baseIdeal_le_kernel p k B A r
        (EnvelopeThickeningP.EnvelopeThickening.polynomialReduction_base p k B))).dpow_comp x hx

theorem envelope_reduction_base : (rE).comp (algebraMap W E) =
    (algebraMap k B).comp WittVector.constantCoeff := by
  ext w
  change rE (PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ I (algebraMap W A w)) = _
  rw [EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_ofAlgebra]
  exact DFunLike.congr_fun (EnvelopeThickeningP.EnvelopeThickening.polynomialReduction_base p k B) w

/-- The polynomial frame modulo p to a positive power. -/
def frame (n : ℕ) : PD.Thickening.AffinePDThickening p k B :=
  PadicPDP.PadicPDThickening.thickening p k B E rE
    (EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_surjective p k B A r
      (EnvelopeThickeningP.EnvelopeThickening.polynomialReduction_surjective p k B)
      (EnvelopeThickeningP.EnvelopeThickening.polynomialReduction_base p k B))
    (envelope_reduction_base p k B) (envelopeDP p k B) (envelope_baseDP p k B) n

variable (S : PD.Thickening.AffinePDThickening p k B)

def evaluate : E →ₐ[W] S.ring where
  __ := PD.EnvelopeDp.PDEnvelope.evaluate W A I₀ δ₀ I (CrystallineFrame.Lifting.CrystallineFrameLifting.target p k B S)
  commutes' w := (CrystallineFrame.Lifting.CrystallineFrameLifting.polynomialLift p k B S).commutes w

theorem evaluate_reduction : S.reduction.comp (evaluate p k B S).toRingHom = rE :=
  CrystallineFrame.Lifting.CrystallineFrameLifting.target_reduction p k B S

theorem evaluate_isDPMorphism :
    DividedPowers.IsDPMorphism (envelopeDP p k B) S.dividedPowers (evaluate p k B S).toRingHom where
  ideal_comp := by
    rw [hE]
    exact (PD.EnvelopeDp.PDEnvelope.evaluate_isDPMorphism W A I₀ δ₀ I
      (CrystallineFrame.Lifting.CrystallineFrameLifting.target p k B S)).ideal_comp
  dpow_comp x hx := by
    have hx' : x ∈ J := hE ▸ hx
    exact (PD.EnvelopeDp.PDEnvelope.evaluate_isDPMorphism W A I₀ δ₀ I
      (CrystallineFrame.Lifting.CrystallineFrameLifting.target p k B S)).dpow_comp x hx'

def frameMorphism (n : ℕ) (hn : (p : S.ring) ^ (n + 1) = 0) : frame p k B n ⟶ S :=
  PadicPDP.PadicPDThickening.morphism p k B E rE
    (EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_surjective p k B A r
      (EnvelopeThickeningP.EnvelopeThickening.polynomialReduction_surjective p k B)
      (EnvelopeThickeningP.EnvelopeThickening.polynomialReduction_base p k B))
    (envelope_reduction_base p k B) (envelopeDP p k B) (envelope_baseDP p k B)
    S (evaluate p k B S) (evaluate_reduction p k B S) (evaluate_isDPMorphism p k B S) n hn

theorem exists_frameMorphism : ∃ n : ℕ, Nonempty (frame p k B n ⟶ S) := by
  obtain ⟨n, hn⟩ := S.p_nilpotent
  exact ⟨n, ⟨frameMorphism p k B S n (by rw [pow_succ, hn, zero_mul])⟩⟩

variable (X : Over (Spec (CommRingCat.of k))) (Q : Cohomology.Site.Object p k X)

/-- A p-power frame on the same affine open as a crystalline object. -/
def siteFrame (n : ℕ) : Cohomology.Site.Object p k X where
  residueRing := Q.residueRing
  thickening := frame p k Q.residueRing n
  immersion := Q.immersion
  openImmersion := Q.openImmersion
  over_base := Q.over_base

def siteFrameMorphism (n : ℕ) (hn : (p : Q.thickening.ring) ^ (n + 1) = 0) :
    Q ⟶ siteFrame p k X Q n where
  reducedMap := AlgHom.id k Q.residueRing
  ambientMap := (frameMorphism p k Q.residueRing Q.thickening n hn).hom
  reduction_comm a := DFunLike.congr_fun
    (frameMorphism p k Q.residueRing Q.thickening n hn).reduction_comp a
  over_X := by
    change Spec.map (𝟙 Q.residueRing) ≫ Q.immersion = Q.immersion
    simp
  dp_comp := (frameMorphism p k Q.residueRing Q.thickening n hn).dp_comp

/-- Every crystalline-site object maps to a polynomial p-power frame. -/
theorem exists_siteFrameMorphism : ∃ n : ℕ, Nonempty (Q ⟶ siteFrame p k X Q n) := by
  obtain ⟨n, hn⟩ := Q.thickening.p_nilpotent
  exact ⟨n, ⟨siteFrameMorphism p k X Q n (by rw [pow_succ, hn, zero_mul])⟩⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicFrames.PadicCrystallineFrames
