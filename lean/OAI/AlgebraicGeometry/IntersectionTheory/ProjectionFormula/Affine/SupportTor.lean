import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilinearLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportTor

/-! # Support Tor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportTor

noncomputable section

/-! Native geometric Tor lengths on an affine scheme equal the
actual localized lengths of the Tor modules of its defining prime
quotients. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk

variable (R : Type) [CommRing R]

theorem length (q s p : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) (hsp : s.asIdeal ≤ p.asIdeal)
    (n : ℕ) :
    CycleClass.Thom.IntersectionGeometry.localTorLength (Spec (.of R)) (SupportStalk.support R q) (SupportStalk.support R s) p (SupportStalk.mem R q p hqp) (SupportStalk.mem R s p hsp) n =
      FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal)
        (((Tor (ModuleCat R) n).obj (.of R (R ⧸ q.asIdeal))).obj (.of R (R ⧸ s.asIdeal))) := by
  let S := (Spec (.of R)).presheaf.stalk p
  let : Algebra R S := (StructureSheaf.toStalk R p).hom.toAlgebra
  let : IsLocalization p.asIdeal.primeCompl S := by
    change IsLocalization p.asIdeal.primeCompl ((structurePresheafInCommRingCat R).stalk p)
    infer_instance
  let : Module.Flat R S := IsLocalization.flat S p.asIdeal.primeCompl
  have hnative := Open.SupportTor.length_iso S
    (SupportStalk.moduleEquiv R q p hqp).toModuleIso (SupportStalk.moduleEquiv R s p hsp).toModuleIso n
  have hquot := (QuotientTorBaseChange.torIso R S q.asIdeal s.asIdeal n).toLinearEquiv.length_eq
  have hbase := (ProjectionFormula.Flat.Extension.torBaseChangeIso R S (.of R (R ⧸ q.asIdeal))
    (.of R (R ⧸ s.asIdeal)) n).toLinearEquiv.length_eq
  have hmodel := SemilinearLength.baseChange_length R (Localization.AtPrime p.asIdeal) S
    (StructureSheaf.stalkIso R p)
    (((Tor (ModuleCat R) n).obj (.of R (R ⧸ q.asIdeal))).obj (.of R (R ⧸ s.asIdeal)))
  exact hnative.trans (hquot.trans (hbase.trans hmodel.symm))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportTor
