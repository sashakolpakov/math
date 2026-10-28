import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp

/-! # Envelope -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Envelope.Comparison

noncomputable section

/-!
# IntegralComparison: identification of the two constructed divided-power envelopes

The crystalline presentations use a small semantic envelope, while the
proved differential-form machinery uses an expression quotient. Their
proved universal properties construct inverse divided-power ring maps.
No envelope or cohomological comparison is assumed.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (J : Ideal R) (δ : DividedPowers J) (I : Ideal A)
  (hbase : J.map (algebraMap R A) ≤ I)

local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope.Envelope R A J δ (algebraMap R A) I
local notation "ε" => OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope.envelopeDividedPowers R A J δ (algebraMap R A) I
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R A J δ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R A J δ I

/-- The differential-form envelope is a target for the crystalline envelope. -/
def formsTarget : DividedPower.PowerEnvelope.Target R A J δ (algebraMap R A) I where
  ring := D
  ideal := AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R A J δ I
  dividedPowers := γ
  fromBase := AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ofAlgebra R A J δ I
  mapsIdeal := Ideal.map_le_iff_le_comap.mp (AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.contains R A J δ I)
  baseCompatible := AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.base_isDPMorphism R A J δ I hbase

/-- The crystalline envelope is a target for the differential-form envelope. -/
def smallTarget : AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Target R A J δ I where
  ring := CommRingCat.of E
  algebra := (DividedPower.PowerEnvelope.toEnvelope R A J δ (algebraMap R A) I).toAlgebra
  ideal := DividedPower.PowerEnvelope.envelopeIdeal R A J δ (algebraMap R A) I
  dp := ε
  contains := Ideal.map_le_iff_le_comap.mpr
    (DividedPower.PowerEnvelope.toEnvelope_mapsIdeal R A J δ (algebraMap R A) I)
  baseDP := (DividedPower.PowerEnvelope.envelopeTarget R A J δ (algebraMap R A) I
    (Ideal.map_le_iff_le_comap.mp hbase)).baseCompatible

def toForms : DividedPowers.DPMorphism ε γ :=
  DividedPower.PowerEnvelope.lift R A J δ (algebraMap R A) I (formsTarget R A J δ I hbase)

def fromForms : DividedPowers.DPMorphism γ ε :=
  DividedPowers.DPMorphism.mk'
    (AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.evaluate_isDPMorphism R A J δ I (smallTarget R A J δ I hbase))

theorem toForms_base :
    (toForms R A J δ I hbase).toRingHom.comp
      (DividedPower.PowerEnvelope.toEnvelope R A J δ (algebraMap R A) I) = AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ofAlgebra R A J δ I :=
  DividedPower.PowerEnvelope.lift_fromBase R A J δ (algebraMap R A) I (formsTarget R A J δ I hbase)

theorem fromForms_base :
    (fromForms R A J δ I hbase).toRingHom.comp (AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ofAlgebra R A J δ I) =
      DividedPower.PowerEnvelope.toEnvelope R A J δ (algebraMap R A) I := by
  ext a
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.evaluate_ofAlgebra R A J δ I (smallTarget R A J δ I hbase) a

theorem fromForms_toForms :
    (fromForms R A J δ I hbase).comp (toForms R A J δ I hbase) =
      DividedPowers.DPMorphism.id ε := by
  let T := DividedPower.PowerEnvelope.envelopeTarget R A J δ (algebraMap R A) I
    (Ideal.map_le_iff_le_comap.mp hbase)
  apply (DividedPower.PowerEnvelope.lift_unique R A J δ (algebraMap R A) I T _ ?_).trans
    (DividedPower.PowerEnvelope.lift_unique R A J δ (algebraMap R A) I T _ rfl).symm
  change (fromForms R A J δ I hbase).toRingHom.comp
    ((toForms R A J δ I hbase).toRingHom.comp
      (DividedPower.PowerEnvelope.toEnvelope R A J δ (algebraMap R A) I)) = _
  rw [toForms_base, fromForms_base]
  rfl

theorem toForms_fromForms :
    (toForms R A J δ I hbase).comp (fromForms R A J δ I hbase) =
      DividedPowers.DPMorphism.id γ := by
  let g := (toForms R A J δ I hbase).comp (fromForms R A J δ I hbase)
  have hg : g.toRingHom.comp (AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ofAlgebra R A J δ I) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ofAlgebra R A J δ I := by
    change (toForms R A J δ I hbase).toRingHom.comp
      ((fromForms R A J δ I hbase).toRingHom.comp (AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ofAlgebra R A J δ I)) = _
    rw [fromForms_base, toForms_base]
  let gA : D →ₐ[A] D :=
    { g.toRingHom with commutes' := DFunLike.congr_fun hg }
  have heq : gA = AlgHom.id A D :=
    (AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.lift_unique R A J δ I (AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.envelopeTarget R A J δ I hbase)
      gA g.isDPMorphism).trans
    (AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.lift_unique R A J δ I (AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.envelopeTarget R A J δ I hbase)
      (AlgHom.id A D) (DividedPowers.DPMorphism.id γ).isDPMorphism).symm
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun heq x

/-- The actual two envelope rings are canonically isomorphic. -/
def ringEquiv : E ≃+* D :=
  { (toForms R A J δ I hbase).toRingHom with
    invFun := fromForms R A J δ I hbase
    left_inv := DFunLike.congr_fun (fromForms_toForms R A J δ I hbase)
    right_inv := DFunLike.congr_fun (toForms_fromForms R A J δ I hbase) }

theorem ringEquiv_isDPMorphism :
    DividedPowers.IsDPMorphism ε γ (ringEquiv R A J δ I hbase).toRingHom :=
  (toForms R A J δ I hbase).isDPMorphism

theorem ringEquiv_symm_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (ringEquiv R A J δ I hbase).symm.toRingHom :=
  (fromForms R A J δ I hbase).isDPMorphism

theorem ringEquiv_base (a : A) :
    ringEquiv R A J δ I hbase (DividedPower.PowerEnvelope.toEnvelope R A J δ (algebraMap R A) I a) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ofAlgebra R A J δ I a :=
  DFunLike.congr_fun (toForms_base R A J δ I hbase) a

local instance smallBaseAlgebra : Algebra R E :=
  ((DividedPower.PowerEnvelope.toEnvelope R A J δ (algebraMap R A) I).comp
    (algebraMap R A)).toAlgebra

local instance formsBaseAlgebra : Algebra R D :=
  ((AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ofAlgebra R A J δ I).comp (algebraMap R A)).toAlgebra

/-- The identification respects the original base algebra structure. -/
def algebraEquiv : E ≃ₐ[R] D :=
  { ringEquiv R A J δ I hbase with
    commutes' r := ringEquiv_base R A J δ I hbase (algebraMap R A r) }

theorem algebraEquiv_isDPMorphism :
    DividedPowers.IsDPMorphism ε γ (algebraEquiv R A J δ I hbase).toRingHom :=
  ringEquiv_isDPMorphism R A J δ I hbase

theorem algebraEquiv_symm_isDPMorphism :
    DividedPowers.IsDPMorphism γ ε (algebraEquiv R A J δ I hbase).symm.toRingHom :=
  ringEquiv_symm_isDPMorphism R A J δ I hbase

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Envelope.Comparison
