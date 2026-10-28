import OAI.NumberTheory.PadicHodge.PeriodInvariants.BigEtaleCoherence
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CohomologyCoherence

/-! # Etale Iso Compatibility -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleIsoCompatibility

noncomputable section

/-!
# Agreement with the existing geometric etale action

The new pullback for arbitrary morphisms agrees, on scheme isomorphisms,
with the original exact-equivalence pullback used by the geometric
Galois representation. This agreement uses the actual comparison maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius
open OAI.NumberTheory.PadicHodge.PeriodInvariants.BigProEtaleSite OAI.NumberTheory.PadicHodge.PeriodInvariants.BigEtaleCohomology OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtTransport
open OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence

variable (p : ℕ) [Fact p.Prime]
variable {X Y : Scheme.{u}} (e : X ≅ Y)

omit p [Fact p.Prime] in
instance proEtaleCongr_cocontinuous : (IntegralComparison.ProEtale.proEtaleCongr e).functor.IsCocontinuous
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) :=
  ((IntegralComparison.ProEtale.proEtaleCongr e).toAdjunction.isCocontinuous_iff_coverPreserving
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)).mpr
      (CoverPreserving.of_isContinuous (IntegralComparison.ProEtale.proEtaleCongr e).inverse _ _)

theorem constant_iso :
    ConstantRestrictionCoherence.transport (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) (IntegralComparison.ProEtale.proEtaleCongr e).functor
      (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p)) = IntegralComparison.Etale.Frobenius.constantUnitTransport p e.symm := by
  apply Iso.ext
  apply ConstantSheafCoherence.transportedConstant_hom_ext (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) e.symm
  exact (ConstantRestrictionCoherence.transport_hom_generator (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
    (IntegralComparison.ProEtale.proEtaleCongr e).functor (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p))).trans
      (ConstantSheafCoherence.constantTransport_generators (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) e.symm
        (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p))).symm

def restriction_square : BigEtaleCohomology.pullbackFunctor p e.hom ⋙ BigProEtaleSite.restriction p X ≅
    BigProEtaleSite.restriction p Y ⋙ (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) e.symm).functor :=
  Iso.refl _

theorem constant_square :
    (BigProEtaleSite.restriction p X).mapIso (BigEtaleCohomology.constantTransport p e.hom) ≪≫ BigEtaleCohomology.constantComparison p X =
      (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) e.symm).functor.mapIso
        (BigEtaleCohomology.constantComparison p Y) ≪≫ IntegralComparison.Etale.Frobenius.constantUnitTransport p e.symm := by
  rw [← constant_iso p e]
  exact (ConstantRestrictionCoherence.transport_comp (Scheme.ProEt.topology X) (Scheme.proetaleTopology.over X)
    (Scheme.proetaleTopology.over Y) (Scheme.ProEt.forget X) (Over.map e.hom)
      (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p))).trans
    (ConstantRestrictionCoherence.transport_comp (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
      (Scheme.proetaleTopology.over Y) (IntegralComparison.ProEtale.proEtaleCongr e).functor (Scheme.ProEt.forget Y)
        (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p))).symm

theorem coefficient_square :
    (BigProEtaleSite.restriction p X).mapIso (BigEtaleCohomology.coefficientTransport p e.hom) ≪≫ BigEtaleCohomology.coefficientComparison p X =
      (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) e.symm).functor.mapIso
        (BigEtaleCohomology.coefficientComparison p Y) ≪≫ IntegralComparison.Etale.Frobenius.coefficientSheafTransport p e.symm := by
  apply Iso.ext
  ext U a
  rfl

theorem comparison_pullback_iso (n : ℕ) (x : BigEtaleCohomology.Cohomology p Y n) :
    BigEtaleCohomology.comparison p X n (BigEtaleCohomology.bigPullback p e.hom n x) =
      IntegralComparison.Etale.Frobenius.cohomologyPullback p e n (BigEtaleCohomology.comparison p Y n x) := by
  change ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p) (BigProEtaleSite.restriction p X) (BigEtaleCohomology.constantComparison p X)
    (BigEtaleCohomology.coefficientComparison p X) n
    (ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p) (BigEtaleCohomology.pullbackFunctor p e.hom) (BigEtaleCohomology.constantTransport p e.hom)
      (BigEtaleCohomology.coefficientTransport p e.hom) n x) =
    ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p)
      (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) e.symm).functor
      (IntegralComparison.Etale.Frobenius.constantUnitTransport p e.symm) (IntegralComparison.Etale.Frobenius.coefficientSheafTransport p e.symm) n
      (ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p) (BigProEtaleSite.restriction p Y) (BigEtaleCohomology.constantComparison p Y)
        (BigEtaleCohomology.coefficientComparison p Y) n x)
  rw [ExtTransport.exactTransport_comp, ExtTransport.exactTransport_comp, constant_square, coefficient_square]
  rfl

theorem pullback_iso (n : ℕ) (x : IntegralComparison.Cohomology.RationalEllAdicCohomology p Y n) :
    BigEtaleCohomology.pullback p e.hom n x = IntegralComparison.Etale.Frobenius.cohomologyPullback p e n x := by
  obtain ⟨z, rfl⟩ := (BigEtaleCohomology.comparisonEquiv p Y n).surjective x
  change BigEtaleCohomology.comparison p X n
    (BigEtaleCohomology.bigPullback p e.hom n ((BigEtaleCohomology.comparisonEquiv p Y n).symm (BigEtaleCohomology.comparisonEquiv p Y n z))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact comparison_pullback_iso p e n z

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleIsoCompatibility
