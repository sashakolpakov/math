import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.PrincipalAbelian
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BasisCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.PrincipalSections

/-! # Slice Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceAcyclicity

noncomputable section

/-!
# IntegralComparison: positive cohomology vanishes on every original affine crystalline slice

The actual structure sheaf on a crystalline slice is compared with the
native affine structure sheaf, including the exact coefficient universe.
All comparisons preserve the constant source used by Ext cohomology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens.Category

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of (WittVector p k))} (U : BigCrystallineSite.Object p (WittVector p k) J δ f)

abbrev coefficientSheaf :=
  (Witt.PrincipalAbelian.Comparison.forgetCoefficients p k U).obj
    (CrystallinePrincipal.Modules.zariskiUnitSheaf U)

def componentIso (r : PrincipalOpens.Category.Principal U.ring) :
    (coefficientSheaf p k U).obj.obj (op r) ≅
      (Principal.BasisCohomology.unitSheaf U.ring).obj.obj (op r) :=
  ((AddEquiv.ulift : ULift.{u + 1} (Lifted.PrincipalSections.Sections U.ring r) ≃+
      Lifted.PrincipalSections.Sections U.ring r).trans
    (Lifted.PrincipalSections.sectionsEquiv U.ring r).toAddEquiv).toAddCommGrpIso

omit [CharP k p] in
theorem component_natural {r s : PrincipalOpens.Category.Principal U.ring} (a : r ⟶ s) :
    (coefficientSheaf p k U).obj.map a.op ≫ (componentIso p k U r).hom =
      (componentIso p k U s).hom ≫
        (Principal.BasisCohomology.unitSheaf U.ring).obj.map a.op := by
  apply AddCommGrpCat.hom_ext
  ext x
  exact Lifted.PrincipalSections.sections_natural_apply U.ring a x.down

def coefficientSheafIso : coefficientSheaf p k U ≅ Principal.BasisCohomology.unitSheaf U.ring :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun r => componentIso p k U r.unop)
    (fun a => component_natural p k U a.unop))

def coefficientExtEquiv (n : ℕ) :
    Abelian.Ext.{u + 2} (Principal.BasisCohomology.constantUnit U.ring) (coefficientSheaf p k U) n ≃+
      Abelian.Ext.{u + 2} (Principal.BasisCohomology.constantUnit U.ring)
        (Principal.BasisCohomology.unitSheaf U.ring) n :=
  (((Abelian.extFunctor n).obj (op (Principal.BasisCohomology.constantUnit U.ring))).mapIso
    (coefficientSheafIso p k U)).addCommGroupIsoToAddEquiv

def cohomologyEquiv (n : ℕ) : SliceStructure.Cohomology U n ≃+
    Abelian.Ext.{u + 2} (Principal.BasisCohomology.constantUnit U.ring)
      (Principal.BasisCohomology.unitSheaf U.ring) n :=
  (Witt.PrincipalAbelian.Comparison.sliceCohomologyEquiv p k U n).trans
    (coefficientExtEquiv p k U n)

/-- Actual structure-sheaf Ext cohomology vanishes in positive degree on the slice. -/
theorem positive_cohomology_zero (q : ℕ) :
    Subsingleton (SliceStructure.Cohomology U (q + 1)) := by
  let := Principal.BasisCohomology.positive_cohomology_zero U.ring q
  exact (cohomologyEquiv p k U (q + 1)).toEquiv.subsingleton

def topSectionsEquiv :
    (coefficientSheaf p k U).obj.obj (op (PrincipalOpens.Category.top U.ring)) ≃+ ULift.{u + 1} U.ring := by
  letI : IsLocalization.Away (1 : U.ring) (Lifted.PrincipalSections.Sections U.ring (PrincipalOpens.Category.top U.ring)) :=
    Lifted.PrincipalSections.sectionsLocalization U.ring (PrincipalOpens.Category.top U.ring)
  exact (AddEquiv.ulift : ULift.{u + 1} (Lifted.PrincipalSections.Sections U.ring (PrincipalOpens.Category.top U.ring)) ≃+
      Lifted.PrincipalSections.Sections U.ring (PrincipalOpens.Category.top U.ring)).trans
    (IsLocalization.atUnit U.ring (S := Lifted.PrincipalSections.Sections U.ring (PrincipalOpens.Category.top U.ring))
      (1 : U.ring) isUnit_one).symm.toAddEquiv |>.trans AddEquiv.ulift.symm

/-- Degree zero of the original slice cohomology is its actual ambient ring. -/
def degreeZeroEquiv : SliceStructure.Cohomology U 0 ≃+ ULift.{u + 1} U.ring :=
  (Witt.PrincipalAbelian.Comparison.sliceCohomologyEquiv p k U 0).trans
    (Sheaf.H.equiv₀.{u + 2, u + 1, u, u} (coefficientSheaf p k U) (PrincipalOpens.Category.isTerminal U.ring)) |>.trans
    (topSectionsEquiv p k U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceAcyclicity
