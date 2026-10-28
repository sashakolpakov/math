import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.HomologyBijective
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology

/-! # Homology Restriction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.HomologyRestriction.SemilinearHomologyRestriction

noncomputable section

/-! # The original cycle-quotient semilinear map equals canonical restricted homology transport -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction

universe u

variable {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S}
  {C : CochainComplex (ModuleCat.{u} R) ℕ} {D : CochainComplex (ModuleCat.{u} S) ℕ}
  (f : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map φ C D)

theorem original (n : ℕ) (x : C.homology n) :
    (Mapped.ComplexHomology.MappedComplexHomology.iso (ModuleCat.restrictScalars φ) D n).hom
        (HomologicalComplex.homologyMap (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap f) n x) =
      NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap f n x := by
  let y := HomologicalComplex.homologyMap (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap f) n x
  let d := (D.sc n).moduleCatLeftHomologyData
  have hb := Mapped.LeftHomologyIso.MappedLeftHomologyIso.homologyIso (ModuleCat.restrictScalars φ) (D.sc n) d
  have ha := (HomologyBijective.SemilinearHomologyBijective.leftData f n).homologyMap_comm
  apply (ConcreteCategory.bijective_of_isIso (D.sc n).moduleCatHomologyIso.hom).injective
  have ht : (D.sc n).moduleCatHomologyIso.hom
      ((Mapped.ComplexHomology.MappedComplexHomology.iso (ModuleCat.restrictScalars φ) D n).hom y) =
        (d.map (ModuleCat.restrictScalars φ)).homologyIso.hom y :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hb) y
  have hc : (d.map (ModuleCat.restrictScalars φ)).homologyIso.hom y =
      NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.quotientMap f n ((C.sc n).moduleCatHomologyIso.hom x) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ha) x
  exact (ht.trans hc).trans (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap_quotient f n x).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.HomologyRestriction.SemilinearHomologyRestriction
