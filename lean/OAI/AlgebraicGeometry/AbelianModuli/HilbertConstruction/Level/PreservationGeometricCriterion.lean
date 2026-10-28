import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Scheme

/-! # Preservation Geometric Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationGeometricCriterion

noncomputable section

/-! Preservation of a full ordered level on all test schemes is equivalent to equality of two maps from the finite constant level scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g N : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}

theorem fullLevel_point_from_geometric (l : A.FullLevel N) (T : Over S)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    (Level.Scheme.constantFullLevelRepresentable g N S).homEquiv.symm c ≫ l.schemeIso.hom ≫ A.torsionInclusion N =
      (l.hom.app (.op T) c).val := by
  let r := (Level.Scheme.constantFullLevelRepresentable g N S).homEquiv.symm c
  let z := (Level.Scheme.constantFullLevelRepresentable g N S).homEquiv (𝟙 (Level.Scheme.constantFullLevelScheme g N S))
  have hc : (Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S).map r.op z = c := by
    change ((Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ⋙ forget GrpCat).map r.op) z = c
    rw [← (Level.Scheme.constantFullLevelRepresentable g N S).homEquiv_comp, Category.comp_id]
    exact (Level.Scheme.constantFullLevelRepresentable g N S).homEquiv.apply_symm_apply c
  have hn := ConcreteCategory.congr_hom (l.hom.naturality r.op) z
  change l.hom.app (.op T) ((Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S).map r.op z) =
    (A.torsionFunctor N).map r.op (l.hom.app (.op (Level.Scheme.constantFullLevelScheme g N S)) z) at hn
  rw [hc] at hn
  rw [l.schemeIso_hom_basis]
  exact congrArg Subtype.val hn.symm

theorem fullLevel_preserves_iff_geometric (l : A.FullLevel N) (k : B.FullLevel N)
    (f : A.scheme ⟶ B.scheme) :
    (∀ (T : Over S) (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
      (l.hom.app (.op T) c).val ≫ f = (k.hom.app (.op T) c).val) ↔
      l.schemeIso.hom ≫ A.torsionInclusion N ≫ f = k.schemeIso.hom ≫ B.torsionInclusion N := by
  constructor
  · intro h
    rw [← Category.assoc, l.schemeIso_hom_basis, k.schemeIso_hom_basis]
    exact h _ _
  · intro h T c
    rw [← fullLevel_point_from_geometric l T c, ← fullLevel_point_from_geometric k T c]
    simpa only [Category.assoc] using congrArg
      (fun z => (Level.Scheme.constantFullLevelRepresentable g N S).homEquiv.symm c ≫ z) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationGeometricCriterion
