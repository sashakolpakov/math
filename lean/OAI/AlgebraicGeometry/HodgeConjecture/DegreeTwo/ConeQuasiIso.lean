import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Cone Quasi Iso -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ConeQuasiIso.Constructions

noncomputable section

/-! An actual cochain comparison is a quasi-isomorphism precisely when its actual cone is exact. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

theorem cochainQuasiIso_iff_mappingCone_acyclic {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  change HomologicalComplex.quasiIso C (ComplexShape.up ℤ) f ↔ _
  rw [← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

theorem functorQuasiIso_of_mappingCone_acyclic (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (h : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone f)).Acyclic) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  apply (cochainQuasiIso_iff_mappingCone_acyclic _).mpr
  intro n
  exact (h n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso f F)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ConeQuasiIso.Constructions
