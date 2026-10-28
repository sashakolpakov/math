import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobenius

/-! # Polynomial Frame Frobenius -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialFrameFrobenius.WittPolynomialFrameFrobenius

noncomputable section

/-! # The semilinear Frobenius lift on the original completed crystalline frame forms -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B P r hr hb
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B P r hr hb
local notation "φ" => WittVector.frobeniusEquiv p k
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.levelMap p k σ
local notation "f" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ

theorem formsMap_transition (j n m : ℕ) (h : n ≤ m)
    (ω : PD.PDDeRham.Form p k B Tower j m) :
    f n j (PD.PDDeRham.transition p k B Tower j n m h ω) =
      PD.PDDeRham.transition p k B Tower j n m h (f m j ω) := by
  let t : (T m).ring →ₐ[W] (T n).ring := (PD.InverseLimit.PDInverseLimit.transition p k B Tower n m h).hom
  let g : PD.PDDeRham.Form p k B Tower j m →+
      PD.PDDeRham.Form p k B Tower j n :=
    (f n j).toAddMonoidHom.comp (PD.PDDeRham.transition p k B Tower j n m h).toAddMonoidHom
  let l : PD.PDDeRham.Form p k B Tower j m →+
      PD.PDDeRham.Form p k B Tower j n :=
    (PD.PDDeRham.transition p k B Tower j n m h).toAddMonoidHom.comp (f m j).toAddMonoidHom
  have ht (a : (T m).ring) (v : Fin j → (T m).ring) :
      PD.PDDeRham.transition p k B Tower j n m h
        (PD.DeRham.PDDeRham.symbol W (T m).ring (RingHom.ker (T m).reduction) (T m).dividedPowers a v) =
      PD.DeRham.PDDeRham.symbol W (T n).ring (RingHom.ker (T n).reduction) (T n).dividedPowers (t a) (t ∘ v) :=
    PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (CommAlgCat.ofHom t)
      (PD.InverseLimit.PDInverseLimit.transition p k B Tower n m h).dp_comp j a v
  have hh : g = l := PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.addHom_ext W (T m).ring
    (RingHom.ker (T m).reduction) (T m).dividedPowers j g l (by
      intro a v
      have hleft := (congrArg (f n j) (ht a v)).trans
        (FrameFrobenius.WittPolynomialFrameFrobenius.formsMap_symbol p k σ n j (t a) (t ∘ v))
      have hright := (congrArg (PD.PDDeRham.transition p k B Tower j n m h)
        (FrameFrobenius.WittPolynomialFrameFrobenius.formsMap_symbol p k σ m j a v)).trans
          (ht (F m a) (F m ∘ v))
      have hmid := congrArg₂ (PD.DeRham.PDDeRham.symbol W (T n).ring (RingHom.ker (T n).reduction) (T n).dividedPowers)
        (FrameFrobenius.WittPolynomialFrameFrobenius.levelMap_transition p k σ n m h a)
        (funext (fun i => FrameFrobenius.WittPolynomialFrameFrobenius.levelMap_transition p k σ n m h (v i)))
      exact hleft.trans (hmid.trans hright.symm))
  exact DFunLike.congr_fun hh ω

def formMap (j : ℕ) : PD.PDDeRham.CompletedForm p k B Tower j →ₛₗ[(φ).toRingHom]
    PD.PDDeRham.CompletedForm p k B Tower j where
  toFun ω := ⟨fun n => f n j (ω.val n), by
    intro n m h
    exact (formsMap_transition p k σ j n m h (ω.val m)).symm.trans
      (congrArg (f n j) (ω.property n m h))⟩
  map_add' ω η := PD.PDDeRham.ext p k B Tower (fun n => (f n j).map_add (ω.val n) (η.val n))
  map_smul' w ω := PD.PDDeRham.ext p k B Tower (fun n => (f n j).map_smulₛₗ w (ω.val n))

theorem eval_formMap (j n : ℕ) (ω : PD.PDDeRham.CompletedForm p k B Tower j) :
    PD.PDDeRham.eval p k B Tower j n (formMap p k σ j ω) =
      f n j (PD.PDDeRham.eval p k B Tower j n ω) := rfl

theorem formMap_differential (j : ℕ) (ω : PD.PDDeRham.CompletedForm p k B Tower j) :
    formMap p k σ (j + 1) (PD.PDDeRham.differential p k B Tower j ω) =
      PD.PDDeRham.differential p k B Tower j (formMap p k σ j ω) := by
  apply PD.PDDeRham.ext p k B Tower
  intro n
  rw [eval_formMap, PD.PDDeRham.eval_differential, PD.PDDeRham.eval_differential,
    eval_formMap]
  exact PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap_differential W W (T n).ring (T n).ring (φ).toRingHom
    (F n) (FrameFrobenius.WittPolynomialFrameFrobenius.levelMap_base p k σ n)
    (RingHom.ker (T n).reduction) (T n).dividedPowers
    (RingHom.ker (T n).reduction) (T n).dividedPowers
    (FrameFrobenius.WittPolynomialFrameFrobenius.levelMap_isDPMorphism p k σ n) j _

def complexMap : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map (φ).toRingHom
    (PD.PDDeRham.complex p k B Tower) (PD.PDDeRham.complex p k B Tower) :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.ofSuccessors (fun j => formMap p k σ j) (by
    intro j ω
    dsimp only [PD.PDDeRham.complex]
    rw [CochainComplex.of_d]
    exact formMap_differential p k σ j ω)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialFrameFrobenius.WittPolynomialFrameFrobenius
