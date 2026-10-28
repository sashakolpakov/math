import OAI.NumberTheory.PadicHodge.IntegralComparison.Envelope
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence

/-! # Envelope Forms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EnvelopeForms

noncomputable section

/-!
# IntegralComparison: differential forms on the actual crystalline envelope

The proved envelope identification induces an isomorphism of the actual
divided-power de Rham complexes, including their differentials.
-/

open _root_.CategoryTheory

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (J : Ideal R) (δ : DividedPowers J) (I : Ideal A)
  (hbase : J.map (algebraMap R A) ≤ I)

attribute [local instance] Envelope.Comparison.smallBaseAlgebra
  Envelope.Comparison.formsBaseAlgebra

local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope.Envelope R A J δ (algebraMap R A) I
local notation "IE" => OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope.envelopeIdeal R A J δ (algebraMap R A) I
local notation "ε" => OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope.envelopeDividedPowers R A J δ (algebraMap R A) I
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R A J δ I
local notation "ID" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R A J δ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R A J δ I
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Envelope.Comparison.algebraEquiv R A J δ I hbase
local notation "he" => OAI.NumberTheory.PadicHodge.IntegralComparison.Envelope.Comparison.algebraEquiv_isDPMorphism R A J δ I hbase
local notation "hi" => OAI.NumberTheory.PadicHodge.IntegralComparison.Envelope.Comparison.algebraEquiv_symm_isDPMorphism R A J δ I hbase

/-- The comparison of differential forms in every degree. -/
def formsEquiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R E IE ε n ≃ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R D ID γ n :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv (A := CommAlgCat.of R E) (B := CommAlgCat.of R D)
    e he hi n

theorem formsEquiv_D (x : E) :
    formsEquiv R A J δ I hbase 1 (AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R E IE ε x) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R D ID γ (e x) :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv_D (A := CommAlgCat.of R E) (B := CommAlgCat.of R D)
    e he hi x

theorem formsEquiv_differential (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R E IE ε n) :
    formsEquiv R A J δ I hbase (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R E IE ε n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R D ID γ n (formsEquiv R A J δ I hbase n ω) :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv_differential
    (A := CommAlgCat.of R E) (B := CommAlgCat.of R D) e he hi n ω

/-- The envelope identification is an isomorphism of de Rham complexes. -/
def complexIso : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R E IE ε ≅ AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R D ID γ :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence.complexIso (A := CommAlgCat.of R E) (B := CommAlgCat.of R D)
    e he hi

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EnvelopeForms
