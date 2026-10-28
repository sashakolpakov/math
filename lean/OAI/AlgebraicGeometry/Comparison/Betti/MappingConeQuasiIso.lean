import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Mapping Cone Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MappingConeQuasiIso.Ext

noncomputable section

/-! A morphism is a quasi-isomorphism exactly when its actual mapping cone is acyclic. -/

open _root_.CategoryTheory _root_.HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

theorem quasiIso_iff_mappingCone_acyclic :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

end

end OAI.AlgebraicGeometry.Comparison.Betti.MappingConeQuasiIso.Ext
