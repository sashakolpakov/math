import OAI.RepresentationTheory.Theta.Geometric.PrincipalUnitaryDeterminant
import OAI.RepresentationTheory.Theta.Geometric.PrincipalFiniteCoordinates
import OAI.RepresentationTheory.Theta.Geometric.Reference.ModuliPoints

/-! # PEL Finite Matrix -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! An equality of actual reference moduli points yields a rational SU
matrix in the exact finite subgroup, preserving every original label. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x y : D.domain}
    (R : D.ReferencePELPointData hg x) (S : D.ReferencePELPointData hg y)

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.familyIso_of_point_eq (h : R.point = S.point) : Nonempty (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso R.family S.family) := by
  have hS := S.point_family
  rw [← h] at hS
  exact ⟨R.point_family.some.symm.trans hS.some⟩

variable (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso R.family S.family)

def Data.ActiveHeckeThetaData.ReferencePELPointData.rationalMatrix : D.RationalSU :=
  letI : NeZero D.pel.level := ⟨by have h := hg.fullLevel; omega⟩
  PrincipalUnitaryDeterminant.referencePELRationalSU (C := R.polarization) (C' := S.polarization) e hg.fullLevel

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.rationalMatrix_lattice (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    v ∈ D.pel.reference.lattice ↔ D.rationalLinear (R.rationalMatrix S e) v ∈ D.pel.reference.lattice := by
  let : NeZero D.pel.level := ⟨by have h := hg.fullLevel; omega⟩
  exact PrincipalUnitaryDeterminant.referencePELRationalSU_lattice (C := R.polarization) (C' := S.polarization) e hg.fullLevel v

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.rationalMatrix_level (v : D.pel.reference.lattice) :
    ∃ w ∈ D.pel.reference.lattice,
      D.rationalLinear (R.rationalMatrix S e) v.val - v.val = D.pel.level • w := by
  let : NeZero D.pel.level := ⟨by have h := hg.fullLevel; omega⟩
  exact PrincipalUnitaryDeterminant.referencePELRationalSU_level (C := R.polarization) (C' := S.polarization) e hg.fullLevel v

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.rationalMatrix_finite (hc : D.HasFiniteCoordinates) :
    D.rationalFinite (R.rationalMatrix S e) ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup :=
  D.principal_finite_membership hc (R.rationalMatrix S e) (R.rationalMatrix_lattice S e)
    (fun v hv => R.rationalMatrix_level S e ⟨v, hv⟩)

end

end OAI.RepresentationTheory.Theta.Geometric
