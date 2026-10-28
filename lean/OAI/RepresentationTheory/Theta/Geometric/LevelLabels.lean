import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel

/-! # Level Labels -/

namespace OAI.RepresentationTheory.Theta.Geometric.LevelLabels

noncomputable section

/-! An arbitrary prescribed ordering of the actual complex torsion
points extends to a native full level on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel

variable {g N : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)

def fullLevelPointEquiv (l : A.FullLevel N) :
    Multiplicative (Fin (2 * g) → ZMod N) ≃* A.torsionPoints N (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :=
  (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel.constantValuesEquiv _).trans ((l.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))).groupIsoToMulEquiv)

def relabelFullLevel (l : A.FullLevel N)
    (ec : Multiplicative (Fin (2 * g) → ZMod N) ≃*
      A.torsionPoints N (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) : A.FullLevel N :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupIsomorphisms.constantGroupIsoOfLabels
    (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase (ec.trans (fullLevelPointEquiv A l).symm)) ≪≫ l

theorem relabelFullLevel_points (l : A.FullLevel N)
    (ec : Multiplicative (Fin (2 * g) → ZMod N) ≃*
      A.torsionPoints N (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) :
    fullLevelPointEquiv A (relabelFullLevel A l ec) = ec := by
  apply MulEquiv.ext
  intro a
  change l.hom.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
    (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ((fullLevelPointEquiv A l).symm (ec a))) = ec a
  exact (fullLevelPointEquiv A l).apply_symm_apply (ec a)

theorem exists_fullLevel_with_labels
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom) [NeZero N]
    (ec : Multiplicative (Fin (2 * g) → ZMod N) ≃*
      A.torsionPoints N (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) :
    ∃ l : A.FullLevel N, fullLevelPointEquiv A l = ec :=
  ⟨relabelFullLevel A (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel.fullLevel A P N) ec,
    relabelFullLevel_points A (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel.fullLevel A P N) ec⟩

theorem fullLevelMap_ext_on_complex {d : ℕ} (l : A.FullLevel N)
    {α β : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor d N AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ A.torsionFunctor N}
    (h : ∀ a : Multiplicative (Fin (2 * d) → ZMod N),
      α.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a) =
        β.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)) : α = β := by
  have he : α ≫ l.inv = β ≫ l.inv := by
    apply AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupMap_ext
    intro z
    apply MonoidHom.ext
    intro a
    change LocallyConstant.toFun (l.inv.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
      (α.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a))) z =
      LocallyConstant.toFun (l.inv.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
        (β.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a))) z
    rw [h a]
  have hc := congrArg (fun t => t ≫ l.hom) he
  simpa only [Category.assoc, l.inv_hom_id, Category.comp_id] using hc

end

end OAI.RepresentationTheory.Theta.Geometric.LevelLabels
