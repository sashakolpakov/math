import OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeFactor

/-! # Lifting -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Lifting.CrystallineFrameLifting

noncomputable section

/-!
# Cohomology: lifting an affine crystalline object into a polynomial frame

The surjective reduction of an actual crystalline thickening lifts each
polynomial generator. The relative envelope then extends this lift, and
nilpotence factors it through a finite envelope truncation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
variable (B : Type u) [CommRing B] [Algebra k B]
variable (S : PD.Thickening.AffinePDThickening p k B)

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

/-- Lift the polynomial generators using the surjective reduction map. -/
def polynomialLift : A →ₐ[W] S.ring :=
  MvPolynomial.aeval (Function.surjInv S.reduction_surjective)

/-- The lift has exactly the prescribed reduction. -/
theorem polynomialLift_reduction : S.reduction.comp (polynomialLift p k B S).toRingHom = r := by
  apply MvPolynomial.ringHom_ext
  · intro w
    change S.reduction (MvPolynomial.aeval (Function.surjInv S.reduction_surjective)
      (MvPolynomial.C w)) =
        MvPolynomial.eval₂Hom ((algebraMap k B).comp WittVector.constantCoeff) id (MvPolynomial.C w)
    rw [MvPolynomial.aeval_C, MvPolynomial.eval₂Hom_C]
    exact DFunLike.congr_fun S.reduction_base w
  · intro b
    change S.reduction (MvPolynomial.aeval (Function.surjInv S.reduction_surjective)
      (MvPolynomial.X b)) =
        MvPolynomial.eval₂Hom ((algebraMap k B).comp WittVector.constantCoeff) id (MvPolynomial.X b)
    rw [MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X']
    exact Function.rightInverse_surjInv S.reduction_surjective b

/-- The actual thickening, regarded as a target of the polynomial frame's relative envelope. -/
def target : PD.EnvelopeDp.PDEnvelope.Target W A I₀ δ₀ I := by
  let : Algebra A S.ring := (polynomialLift p k B S).toRingHom.toAlgebra
  refine
    { ring := S.ring
      ideal := RingHom.ker S.reduction
      dp := S.dividedPowers
      contains := ?_
      baseDP := ?_ }
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change S.reduction (polynomialLift p k B S a) = 0
    exact (DFunLike.congr_fun (polynomialLift_reduction p k B S) a).trans ha
  · have h : (algebraMap A S.ring).comp (algebraMap W A) = algebraMap W S.ring := by
      ext w
      exact (polynomialLift p k B S).commutes w
    rw [h]
    exact S.baseDP

/-- Every affine thickening with nilpotent defining ideal receives a unique divided-power map
from some finite truncation of its lifted polynomial frame. -/
theorem exists_truncated_lift (hS : IsNilpotent (RingHom.ker S.reduction)) :
    ∃ n : ℕ, ∃! g : PD.Truncation.PDTruncation.Ring E J n →ₐ[A] (target p k B S).ring,
      DividedPowers.IsDPMorphism (PD.Truncation.PDTruncation.dividedPowers E J δ n)
        (target p k B S).dp g.toRingHom :=
  PD.EnvelopeFactor.PDEnvelopeFactor.exists_truncated_lift W A I₀ δ₀ I (target p k B S) hS

/-- Evaluation in the thickening commutes with its residual-algebra map. -/
theorem target_reduction :
    S.reduction.comp (PD.EnvelopeDp.PDEnvelope.evaluate W A I₀ δ₀ I (target p k B S)) = rE := by
  apply PD.EnvelopeDp.PDEnvelope.ringHom_ext W A I₀ δ₀ I
  · intro a
    change S.reduction (PD.EnvelopeDp.PDEnvelope.evaluate W A I₀ δ₀ I (target p k B S)
      (PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ I a)) = rE (PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ I a)
    rw [PD.EnvelopeDp.PDEnvelope.evaluate_ofAlgebra, EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_ofAlgebra]
    exact DFunLike.congr_fun (polynomialLift_reduction p k B S) a
  · intro t
    have hl : S.reduction (PD.EnvelopeDp.PDEnvelope.evaluate W A I₀ δ₀ I (target p k B S)
        (PD.EnvelopeDp.PDEnvelope.idealTerm W A I₀ δ₀ I t)) = 0 :=
      PD.EnvelopeDp.PDEnvelope.evaluate_mem W A I₀ δ₀ I (target p k B S) (Set.mem_range_self t)
    have hr : rE (PD.EnvelopeDp.PDEnvelope.idealTerm W A I₀ δ₀ I t) = 0 := by
      change PD.EnvelopeDp.PDEnvelope.idealTerm W A I₀ δ₀ I t ∈ RingHom.ker rE
      rw [EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_kernel]
      exact Set.mem_range_self t
    change S.reduction (PD.EnvelopeDp.PDEnvelope.evaluate W A I₀ δ₀ I (target p k B S)
      (PD.EnvelopeDp.PDEnvelope.idealTerm W A I₀ δ₀ I t)) = rE (PD.EnvelopeDp.PDEnvelope.idealTerm W A I₀ δ₀ I t)
    rw [hl, hr]

variable (n : ℕ) (hn : (RingHom.ker S.reduction) ^ (n + 1) = 0)

/-- The map from the truncated polynomial frame, with Witt scalars retained. -/
def frameMap : (EnvelopeThickeningP.EnvelopeThickening.polynomialThickening p k B n).ring →ₐ[W] S.ring :=
  { (PD.EnvelopeFactor.PDEnvelopeFactor.liftThrough W A I₀ δ₀ I (target p k B S) n hn).toRingHom with
    commutes' := by
      intro w
      change PD.EnvelopeFactor.PDEnvelopeFactor.liftThrough W A I₀ δ₀ I (target p k B S) n hn
        (Ideal.Quotient.mk (J ^ (n + 1)) (PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ I (algebraMap W A w))) =
          algebraMap W S.ring w
      exact (PD.EnvelopeFactor.PDEnvelopeFactor.liftThrough_mk W A I₀ δ₀ I (target p k B S) n hn _).trans
        ((PD.EnvelopeDp.PDEnvelope.evaluate_ofAlgebra W A I₀ δ₀ I (target p k B S) _).trans
          ((polynomialLift p k B S).commutes w)) }

@[simp]
theorem frameMap_mk (a : E) :
    frameMap p k B S n hn (Ideal.Quotient.mk (J ^ (n + 1)) a) =
      PD.EnvelopeDp.PDEnvelope.evaluate W A I₀ δ₀ I (target p k B S) a := rfl

theorem frameMap_reduction :
    S.reduction.comp (frameMap p k B S n hn).toRingHom =
      (EnvelopeThickeningP.EnvelopeThickening.polynomialThickening p k B n).reduction := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change S.reduction (frameMap p k B S n hn (Ideal.Quotient.mk (J ^ (n + 1)) a)) =
    PD.Truncation.PDTruncation.reduction E J rE hE n (Ideal.Quotient.mk (J ^ (n + 1)) a)
  rw [frameMap_mk, PD.Truncation.PDTruncation.reduction_mk]
  exact DFunLike.congr_fun (target_reduction p k B S) a

theorem frame_kernel :
    RingHom.ker (EnvelopeThickeningP.EnvelopeThickening.polynomialThickening p k B n).reduction =
      PD.Truncation.PDTruncation.ideal E J n :=
  PD.Truncation.PDTruncation.reduction_kernel E J rE hE n

theorem frameMap_isDPMorphism :
    DividedPowers.IsDPMorphism (EnvelopeThickeningP.EnvelopeThickening.polynomialThickening p k B n).dividedPowers
      S.dividedPowers (frameMap p k B S n hn).toRingHom where
  ideal_comp := by
    rw [frame_kernel]
    exact (PD.EnvelopeFactor.PDEnvelopeFactor.liftThrough_isDPMorphism W A I₀ δ₀ I (target p k B S) n hn).ideal_comp
  dpow_comp a ha := by
    rw [frame_kernel] at ha
    exact (PD.EnvelopeFactor.PDEnvelopeFactor.liftThrough_isDPMorphism W A I₀ δ₀ I (target p k B S) n hn).dpow_comp a ha

/-- A morphism of the actual affine divided-power thickenings. -/
def frameMorphism : EnvelopeThickeningP.EnvelopeThickening.polynomialThickening p k B n ⟶ S where
  hom := frameMap p k B S n hn
  reduction_comp := frameMap_reduction p k B S n hn
  dp_comp := frameMap_isDPMorphism p k B S n hn

/-- Every affine object with nilpotent defining ideal admits a morphism from a finite polynomial frame. -/
theorem exists_frameMorphism (hS : IsNilpotent (RingHom.ker S.reduction)) :
    ∃ n : ℕ, Nonempty (EnvelopeThickeningP.EnvelopeThickening.polynomialThickening p k B n ⟶ S) := by
  obtain ⟨n, hn⟩ := hS
  have hn' : (RingHom.ker S.reduction) ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  exact ⟨n, ⟨frameMorphism p k B S n hn'⟩⟩

variable (X : Over (Spec (CommRingCat.of k))) (Q : Cohomology.Site.Object p k X)

/-- The polynomial-frame thickening on the same affine open as a crystalline object. -/
def siteFrame (n : ℕ) : Cohomology.Site.Object p k X :=
  EnvelopeThickeningP.EnvelopeThickening.objectFromAffineOpen p k Q.residueRing X Q.immersion Q.over_base n

/-- The constructed frame map, in the geometric direction of the crystalline site. -/
def siteFrameMorphism (n : ℕ) (hn : (RingHom.ker Q.thickening.reduction) ^ (n + 1) = 0) :
    Q ⟶ siteFrame p k X Q n where
  reducedMap := AlgHom.id k Q.residueRing
  ambientMap := frameMap p k Q.residueRing Q.thickening n hn
  reduction_comm a := DFunLike.congr_fun (frameMap_reduction p k Q.residueRing Q.thickening n hn) a
  over_X := by
    change Spec.map (𝟙 Q.residueRing) ≫ Q.immersion = Q.immersion
    simp
  dp_comp := frameMap_isDPMorphism p k Q.residueRing Q.thickening n hn

/-- Every crystalline object with nilpotent defining ideal maps to an ideal-power frame
on its underlying affine open. -/
theorem exists_siteFrameMorphism (hQ : IsNilpotent (RingHom.ker Q.thickening.reduction)) : ∃ n : ℕ, Nonempty (Q ⟶ siteFrame p k X Q n) := by
  obtain ⟨n, hn⟩ := hQ
  have hn' : (RingHom.ker Q.thickening.reduction) ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  exact ⟨n, ⟨siteFrameMorphism p k X Q n hn'⟩⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Lifting.CrystallineFrameLifting
