import OAI.AlgebraicGeometry.Comparison.Betti.ConstantPullbackNormalization

/-! # Sections Pullback Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SectionsPullbackNormalization

noncomputable section

/-! The adjunction description of global sections agrees with actual sheaf pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {M N : TopCat.{0}} (f : M ⟶ N)

theorem constantHomSectionsLinearEquiv_pullback (F : ConstantSheafSections.ComplexSheaves N)
    (g : ConstantSheafSections.standardConstantSheaf N ⟶ F) :
    ConstantSheafSections.constantHomSectionsLinearEquiv ((TopologicalSheafPullback.sheafInverseImage f).obj F)
        ((TopologicalSheafPullback.constantPullbackIso f).inv ≫ (TopologicalSheafPullback.sheafInverseImage f).map g) =
      (TopologicalSheafPullback.globalSectionPullback f).app F (ConstantSheafSections.constantHomSectionsLinearEquiv F g) := by
  let a := constantSheafAdj (Opens.grothendieckTopology N) (ModuleCat.{0} ℂ) isTerminalTop
  let b := TopologicalSheafPullback.sheafImageAdjunction f
  let g' := (TopologicalSheafPullback.constantPullbackIso f).inv ≫ (TopologicalSheafPullback.sheafInverseImage f).map g
  have h := ConstantPullbackNormalization.constantPullbackIso_homEquiv f ((TopologicalSheafPullback.sheafInverseImage f).obj F) g'
  have hc : (TopologicalSheafPullback.constantPullbackIso f).hom ≫ g' = (TopologicalSheafPullback.sheafInverseImage f).map g :=
    (TopologicalSheafPullback.constantPullbackIso f).hom_inv_id_assoc _
  have hb : b.homEquiv _ _ ((TopologicalSheafPullback.sheafInverseImage f).map g) = g ≫ b.unit.app F := by
    simpa only [Category.comp_id, b.homEquiv_id] using
      b.homEquiv_naturality_left g (𝟙 ((TopologicalSheafPullback.sheafInverseImage f).obj F))
  erw [hc, hb, a.homEquiv_naturality_right g (b.unit.app F)] at h
  exact (congrArg (fun k => k 1) h).symm

theorem constantHomSectionsLinearEquiv_symm_pullback (F : ConstantSheafSections.ComplexSheaves N)
    (s : F.obj.obj (op ⊤)) :
    (ConstantSheafSections.constantHomSectionsLinearEquiv ((TopologicalSheafPullback.sheafInverseImage f).obj F)).symm
        ((TopologicalSheafPullback.globalSectionPullback f).app F s) =
      (TopologicalSheafPullback.constantPullbackIso f).inv ≫
        (TopologicalSheafPullback.sheafInverseImage f).map ((ConstantSheafSections.constantHomSectionsLinearEquiv F).symm s) := by
  apply (ConstantSheafSections.constantHomSectionsLinearEquiv ((TopologicalSheafPullback.sheafInverseImage f).obj F)).injective
  erw [LinearEquiv.apply_symm_apply, constantHomSectionsLinearEquiv_pullback,
    LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.Comparison.Betti.SectionsPullbackNormalization
