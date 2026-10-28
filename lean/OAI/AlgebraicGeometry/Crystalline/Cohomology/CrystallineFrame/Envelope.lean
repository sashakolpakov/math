import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialEval
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ShiftedPolynomialComplex

/-! # Envelope -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Envelope.CrystallineFrameEnvelope

noncomputable section

/-!
# The canonical reduction kernel of the actual crystalline frame

The polynomial reduction sends coefficients by the actual crystalline
reduction and variables to the fixed residual frame coordinates. Its
kernel equals the shifted-coordinate ideal for any chosen lifts.
Consequently the actual relative PD envelope is the free relative PD
algebra used in the native frame extension.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))

local notation "R" => Q.thickening.ring
local notation "P" => MvPolynomial σ R
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "I" => RingHom.ker Q.thickening.reduction
local notation "δ" => Q.thickening.dividedPowers
local notation "x" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Lifts.CrystallineFrameLifts.lift p k B σ a Q

/-- Reduction is defined from the residual coordinates, without using a choice of lifts. -/
def reduction : P →+* Q.residueRing :=
  MvPolynomial.eval₂Hom Q.thickening.reduction
    (fun i => AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q (a i))

theorem reduction_eq : CrystallineFrameEnvelope.reduction p k B σ a Q =
    ShiftedPolynomialEval.ShiftedPolynomialKernel.reduction R σ x Q.residueRing Q.thickening.reduction := by
  apply MvPolynomial.ringHom_ext
  · intro t
    exact (MvPolynomial.eval₂Hom_C _ _ t).trans
      (ShiftedPolynomialEval.ShiftedPolynomialKernel.reduction_C R σ x Q.residueRing Q.thickening.reduction t).symm
  · intro i
    exact (MvPolynomial.eval₂Hom_X' _ _ i).trans
      ((Lifts.CrystallineFrameLifts.reduction_lift p k B σ a Q i).symm.trans
        (ShiftedPolynomialEval.ShiftedPolynomialKernel.reduction_X R σ x Q.residueRing Q.thickening.reduction i).symm)

theorem reduction_surjective : Function.Surjective (CrystallineFrameEnvelope.reduction p k B σ a Q) := by
  rw [reduction_eq]
  exact ShiftedPolynomialEval.ShiftedPolynomialKernel.reduction_surjective R σ x Q.residueRing Q.thickening.reduction
    Q.thickening.reduction_surjective

theorem kernel_eq : RingHom.ker (CrystallineFrameEnvelope.reduction p k B σ a Q) =
    ShiftedPolynomialDP.ShiftedPolynomialEnvelope.polynomialIdeal R σ I x := by
  rw [reduction_eq, ShiftedPolynomialEval.ShiftedPolynomialKernel.reduction_kernel]

local instance envelopeBaseAlgebra (J : Ideal P) : Algebra R (PD.EnvelopeDp.PDEnvelope.Envelope R P I δ J) :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ J).comp (algebraMap R P)).toAlgebra

def envelopeEquiv (J : Ideal P) (hJ : J = ShiftedPolynomialDP.ShiftedPolynomialEnvelope.polynomialIdeal R σ I x) :
    PD.EnvelopeDp.PDEnvelope.Envelope R P I δ J ≃ₐ[R] G := by
  subst J
  exact ShiftedPolynomialDP.ShiftedPolynomialEnvelope.algebraEquiv R σ I δ x

theorem envelopeEquiv_ofAlgebra (J : Ideal P) (hJ : J = ShiftedPolynomialDP.ShiftedPolynomialEnvelope.polynomialIdeal R σ I x)
    (t : P) : envelopeEquiv p k B σ a Q J hJ (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ J t) =
      ShiftedPolynomialDP.ShiftedPolynomialEnvelope.polynomialMap R σ x t := by
  subst J
  exact ShiftedPolynomialDP.ShiftedPolynomialEnvelope.toDivided_ofAlgebra R σ I δ x t

theorem envelopeEquiv_isDPMorphism (J : Ideal P) (hJ : J = ShiftedPolynomialDP.ShiftedPolynomialEnvelope.polynomialIdeal R σ I x) :
    DividedPowers.IsDPMorphism (PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ J)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ) (envelopeEquiv p k B σ a Q J hJ).toRingHom := by
  subst J
  exact ShiftedPolynomialDP.ShiftedPolynomialEnvelope.algebraEquiv_isDPMorphism R σ I δ x

theorem envelopeEquiv_symm_isDPMorphism (J : Ideal P) (hJ : J = ShiftedPolynomialDP.ShiftedPolynomialEnvelope.polynomialIdeal R σ I x) :
    DividedPowers.IsDPMorphism (FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ)
      (PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ J) (envelopeEquiv p k B σ a Q J hJ).symm.toRingHom := by
  subst J
  exact ShiftedPolynomialDP.ShiftedPolynomialEnvelope.algebraEquiv_symm_isDPMorphism R σ I δ x

/-- The envelope uses the exact kernel of the canonical residual-coordinate reduction. -/
def canonicalEquiv : PD.EnvelopeDp.PDEnvelope.Envelope R P I δ (RingHom.ker (CrystallineFrameEnvelope.reduction p k B σ a Q)) ≃ₐ[R] G :=
  envelopeEquiv p k B σ a Q _ (kernel_eq p k B σ a Q)

theorem canonicalEquiv_coordinate (i : σ) :
    canonicalEquiv p k B σ a Q
      (PD.EnvelopeDp.PDEnvelope.ofAlgebra R P I δ (RingHom.ker (CrystallineFrameEnvelope.reduction p k B σ a Q)) (MvPolynomial.X i)) =
        Map.CrystallineFrameMap.coordinate a Q i := by
  rw [canonicalEquiv, envelopeEquiv_ofAlgebra, ShiftedPolynomialDP.ShiftedPolynomialEnvelope.polynomialMap_X]
  rfl

/-- Actual PD forms of the canonical envelope satisfy relative Poincaré. -/
def homotopyEquiv [Fintype σ] : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R))
    (PD.DeRham.PDDeRham.complex R (PD.EnvelopeDp.PDEnvelope.Envelope R P I δ (RingHom.ker (CrystallineFrameEnvelope.reduction p k B σ a Q)))
      (PD.EnvelopeDp.PDEnvelope.ideal R P I δ (RingHom.ker (CrystallineFrameEnvelope.reduction p k B σ a Q)))
      (PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ (RingHom.ker (CrystallineFrameEnvelope.reduction p k B σ a Q)))) := by
  rw [kernel_eq]
  exact ShiftedPolynomialComplex.ShiftedPolynomialPoincare.homotopyEquiv R σ I δ x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Envelope.CrystallineFrameEnvelope
