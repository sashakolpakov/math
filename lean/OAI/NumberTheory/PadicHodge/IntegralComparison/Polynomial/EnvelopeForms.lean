import OAI.NumberTheory.PadicHodge.IntegralComparison.EnvelopeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms

/-! # Envelope Forms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.EnvelopeForms

noncomputable section

/-!
# IntegralComparison: finite free forms on polynomial crystalline envelopes

For every polynomial presentation ideal containing the base ideal, the
actual crystalline envelope has a basis of forms indexed by coordinate
wedges. These statements allow torsion in the coefficient ring.
-/

open _root_.CategoryTheory

universe u

variable (R σ : Type u) [CommRing R]
  (J : Ideal R) (δ : DividedPowers J) (I : Ideal (MvPolynomial σ R))
  (hbase : J.map (algebraMap R (MvPolynomial σ R)) ≤ I)

attribute [local instance] Envelope.Comparison.smallBaseAlgebra
  Envelope.Comparison.formsBaseAlgebra

local notation "P" => MvPolynomial σ R
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope.Envelope R P J δ (algebraMap R P) I
local notation "IE" => OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope.envelopeIdeal R P J δ (algebraMap R P) I
local notation "ε" => OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope.envelopeDividedPowers R P J δ (algebraMap R P) I
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P J δ I
local notation "ID" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P J δ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P J δ I
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Envelope.Comparison.algebraEquiv R P J δ I hbase
local notation "he" => OAI.NumberTheory.PadicHodge.IntegralComparison.Envelope.Comparison.algebraEquiv_isDPMorphism R P J δ I hbase
local notation "hi" => OAI.NumberTheory.PadicHodge.IntegralComparison.Envelope.Comparison.algebraEquiv_symm_isDPMorphism R P J δ I hbase

/-- A coordinate-wedge basis over the actual envelope ring. -/
def formBasis [LinearOrder σ] (n : ℕ) :
    Module.Basis (Set.powersetCard σ n) E (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R E IE ε n) := by
  let : Module E (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R D ID γ n) :=
    Module.compHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R D ID γ n) (e).toRingHom
  let g : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R E IE ε n ≃ₗ[E] AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R D ID γ n :=
    { (EnvelopeForms.formsEquiv R P J δ I hbase n).toEquiv with
      map_add' := map_add (EnvelopeForms.formsEquiv R P J δ I hbase n)
      map_smul' a ω := AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_smul
        (CommAlgCat.ofHom (e).toAlgHom) he n a ω }
  let b := AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.formBasis R σ J δ I hbase n
  exact (b.mapCoeffs (e).symm.toRingEquiv (fun c ω => by
    change (e) ((e).symm c) • ω = c • ω
    rw [AlgEquiv.apply_symm_apply])).map g.symm

include hbase

/-- All degrees of forms are free over the original envelope ring. -/
theorem forms_free (n : ℕ) : Module.Free E (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R E IE ε n) := by
  classical
  let : LinearOrder σ := linearOrderOfSTO WellOrderingRel
  exact Module.Free.of_basis (formBasis R σ J δ I hbase n)

/-- A finite polynomial presentation gives finitely generated forms in each degree. -/
theorem forms_finite [Finite σ] (n : ℕ) : Module.Finite E (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R E IE ε n) := by
  classical
  let : LinearOrder σ := linearOrderOfSTO WellOrderingRel
  exact Module.Finite.of_basis (formBasis R σ J δ I hbase n)

/-- The actual complex vanishes above the number of polynomial variables. -/
theorem higher_form_eq_zero [Fintype σ] (n : ℕ) (hn : Fintype.card σ < n)
    (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R E IE ε n) : ω = 0 := by
  apply (EnvelopeForms.formsEquiv R P J δ I hbase n).injective
  rw [map_zero]
  exact AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.higher_form_eq_zero R σ J δ I hbase n hn _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.EnvelopeForms
