import OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicPDP

/-! # Envelope Frames -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames

noncomputable section

/-!
# Crystalline frames of an arbitrary affine lift

The relative PD envelope of a surjective affine presentation, reduced
modulo powers of p, is a tower of actual crystalline thickenings.
A lift of the presentation to any crystalline object induces a PD map
from a sufficiently high level, allowing a different residual algebra.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (B : Type u) [CommRing B] [Algebra k B]
  (A : Type u) [CommRing A] [Algebra (WittVector p k) A]
  (r : A →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) A) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "I₀" => Ideal.span {(p : W)}
local notation "δ₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope W A I₀ δ₀ (RingHom.ker r)
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal W A I₀ δ₀ (RingHom.ker r)
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers W A I₀ δ₀ (RingHom.ker r)
local notation "rE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeThickeningP.EnvelopeThickening.envelopeReduction p k B A r hr hbase

local instance envelopeBaseAlgebra : Algebra W E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ (RingHom.ker r)).comp (algebraMap W A)).toAlgebra

def envelopeDP : DividedPowers (RingHom.ker rE) :=
  DividedPowers.ofRingEquiv (e := RingEquiv.refl E)
    (by
      change (J).map (RingHom.id E) = RingHom.ker rE
      rw [Ideal.map_id]
      exact (EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_kernel p k B A r hr hbase).symm) δ

theorem envelope_baseDP : DividedPowers.IsDPMorphism δ₀
    (envelopeDP p k B A r hr hbase) (algebraMap W E) where
  ideal_comp := by
    rw [EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_kernel]
    exact (PD.EnvelopeDp.PDEnvelope.base_isDPMorphism W A I₀ δ₀ (RingHom.ker r)
      (EnvelopeThickeningP.EnvelopeThickening.baseIdeal_le_kernel p k B A r hbase)).ideal_comp
  dpow_comp a ha :=
    (PD.EnvelopeDp.PDEnvelope.base_isDPMorphism W A I₀ δ₀ (RingHom.ker r)
      (EnvelopeThickeningP.EnvelopeThickening.baseIdeal_le_kernel p k B A r hbase)).dpow_comp a ha

theorem envelope_reduction_base : (rE).comp (algebraMap W E) =
    (algebraMap k B).comp WittVector.constantCoeff := by
  ext w
  change rE (PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ (RingHom.ker r) (algebraMap W A w)) = _
  rw [EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_ofAlgebra]
  exact DFunLike.congr_fun hbase w

/-- The actual affine crystalline frame modulo p to a positive power. -/
def frame (n : ℕ) : PD.Thickening.AffinePDThickening p k B :=
  PadicPDP.PadicPDThickening.thickening p k B E rE
    (EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_surjective p k B A r hr hbase)
    (envelope_reduction_base p k B A r hr hbase)
    (envelopeDP p k B A r hr hbase) (envelope_baseDP p k B A r hr hbase) n

def tower : ℕᵒᵖ ⥤ PD.Thickening.AffinePDThickening p k B :=
  PadicPDP.PadicPDThickening.tower p k B E rE
    (EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_surjective p k B A r hr hbase)
    (envelope_reduction_base p k B A r hr hbase)
    (envelopeDP p k B A r hr hbase) (envelope_baseDP p k B A r hr hbase)

variable (C : Type u) [CommRing C] [Algebra k C]
variable (S : PD.Thickening.AffinePDThickening p k C)
variable (f : B →ₐ[k] C)
variable (l : A →ₐ[WittVector p k] S.ring)
variable (hl : S.reduction.comp l.toRingHom = f.toRingHom.comp r)

/-- The target PD ring with the algebra structure supplied by the chosen lift. -/
def target : PD.EnvelopeDp.PDEnvelope.Target W A I₀ δ₀ (RingHom.ker r) := by
  let : Algebra A S.ring := l.toRingHom.toAlgebra
  refine
    { ring := S.ring
      ideal := RingHom.ker S.reduction
      dp := S.dividedPowers
      contains := ?_
      baseDP := ?_ }
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change S.reduction (l a) = 0
    rw [show S.reduction (l a) = f (r a) from DFunLike.congr_fun hl a]
    rw [show r a = 0 from ha, map_zero]
  · have h : (algebraMap A S.ring).comp (algebraMap W A) = algebraMap W S.ring := by
      ext w
      exact l.commutes w
    rw [h]
    exact S.baseDP

/-- Evaluation of the universal envelope in the target crystalline ring. -/
def evaluate : E →ₐ[W] S.ring where
  __ := PD.EnvelopeDp.PDEnvelope.evaluate W A I₀ δ₀ (RingHom.ker r) (target p k B A r C S f l hl)
  commutes' w := l.commutes w

theorem evaluate_reduction :
    S.reduction.comp (evaluate p k B A r C S f l hl).toRingHom = f.toRingHom.comp rE := by
  apply PD.EnvelopeDp.PDEnvelope.ringHom_ext W A I₀ δ₀ (RingHom.ker r)
  · intro a
    change S.reduction (PD.EnvelopeDp.PDEnvelope.evaluate W A I₀ δ₀ (RingHom.ker r)
      (target p k B A r C S f l hl) (PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ (RingHom.ker r) a)) =
        f (rE (PD.EnvelopeDp.PDEnvelope.ofAlgebra W A I₀ δ₀ (RingHom.ker r) a))
    rw [PD.EnvelopeDp.PDEnvelope.evaluate_ofAlgebra, EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_ofAlgebra]
    exact DFunLike.congr_fun hl a
  · intro t
    have hleft : S.reduction (evaluate p k B A r C S f l hl
        (PD.EnvelopeDp.PDEnvelope.idealTerm W A I₀ δ₀ (RingHom.ker r) t)) = 0 :=
      PD.EnvelopeDp.PDEnvelope.evaluate_mem W A I₀ δ₀ (RingHom.ker r)
        (target p k B A r C S f l hl) (Set.mem_range_self t)
    have hright : rE (PD.EnvelopeDp.PDEnvelope.idealTerm W A I₀ δ₀ (RingHom.ker r) t) = 0 := by
      change PD.EnvelopeDp.PDEnvelope.idealTerm W A I₀ δ₀ (RingHom.ker r) t ∈ RingHom.ker rE
      rw [EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_kernel]
      exact Set.mem_range_self t
    change S.reduction (evaluate p k B A r C S f l hl
      (PD.EnvelopeDp.PDEnvelope.idealTerm W A I₀ δ₀ (RingHom.ker r) t)) =
        f (rE (PD.EnvelopeDp.PDEnvelope.idealTerm W A I₀ δ₀ (RingHom.ker r) t))
    rw [hleft, hright, map_zero]

theorem evaluate_isDPMorphism : DividedPowers.IsDPMorphism
    (envelopeDP p k B A r hr hbase) S.dividedPowers
    (evaluate p k B A r C S f l hl).toRingHom where
  ideal_comp := by
    rw [EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_kernel]
    exact (PD.EnvelopeDp.PDEnvelope.evaluate_isDPMorphism W A I₀ δ₀ (RingHom.ker r)
      (target p k B A r C S f l hl)).ideal_comp
  dpow_comp a ha := by
    have ha' : a ∈ J := EnvelopeThickeningP.EnvelopeThickening.envelopeReduction_kernel p k B A r hr hbase ▸ ha
    exact (PD.EnvelopeDp.PDEnvelope.evaluate_isDPMorphism W A I₀ δ₀ (RingHom.ker r)
      (target p k B A r C S f l hl)).dpow_comp a ha'

def frameMap (n : ℕ) (hn : (p : S.ring) ^ (n + 1) = 0) :
    (frame p k B A r hr hbase n).ring →ₐ[W] S.ring :=
  PadicPDP.PadicPDThickening.lift p k C E S (evaluate p k B A r C S f l hl) n hn

theorem frameMap_reduction (n : ℕ) (hn : (p : S.ring) ^ (n + 1) = 0) :
    S.reduction.comp (frameMap p k B A r hr hbase C S f l hl n hn).toRingHom =
      f.toRingHom.comp (frame p k B A r hr hbase n).reduction := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun (evaluate_reduction p k B A r hr hbase C S f l hl) a

theorem frameMap_isDPMorphism (n : ℕ) (hn : (p : S.ring) ^ (n + 1) = 0) :
    DividedPowers.IsDPMorphism (frame p k B A r hr hbase n).dividedPowers S.dividedPowers
      (frameMap p k B A r hr hbase C S f l hl n hn).toRingHom := by
  apply DividedPowers.IsDPMorphism.of_comp
    (envelopeDP p k B A r hr hbase) (frame p k B A r hr hbase n).dividedPowers S.dividedPowers
    (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n))
    (frameMap p k B A r hr hbase C S f l hl n hn).toRingHom
    (PadicPDP.PadicPDThickening.reduction_kernel p k B E rE (envelopeDP p k B A r hr hbase)
      (envelope_baseDP p k B A r hr hbase) n)
    (PadicPDP.PadicPDThickening.quotient_isDPMorphism p k B E rE (envelopeDP p k B A r hr hbase)
      (envelope_baseDP p k B A r hr hbase) n)
  exact evaluate_isDPMorphism p k B A r hr hbase C S f l hl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames
