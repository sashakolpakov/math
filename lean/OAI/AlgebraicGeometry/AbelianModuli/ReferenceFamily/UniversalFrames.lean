import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.GeometricLevel

/-! # Universal Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFrames.LevelCover

noncomputable section

/-! The universal frame homomorphism is constructed from its actual
torsion sections, with no chosen full level. The split construction is
proved to recover this same morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def torsionSectionExtension
    (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest S)) :
    HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ⟶ A.torsionFunctor N :=
  ConstantSectionsOn.ConstantSections.extendNatTrans (((A.torsionSchemeYonedaIso N).inv.app (.op (ConstantSectionsOn.ConstantSections.baseTest S))).hom.comp h) ≫
    (A.torsionSchemeYonedaIso N).hom

theorem torsionSectionExtension_const
    (h : Frame.Labels.LevelCover.Coefficients g N →* A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest S)) (c : Frame.Labels.LevelCover.Coefficients g N) :
    (torsionSectionExtension A h).app (.op (ConstantSectionsOn.ConstantSections.baseTest S)) (LocallyConstant.const S c) = h c := by
  let h' : Frame.Labels.LevelCover.Coefficients g N →* (ConstantSectionsOn.ConstantSections.baseTest S ⟶ A.torsionScheme N) :=
    ((A.torsionSchemeYonedaIso N).inv.app (.op (ConstantSectionsOn.ConstantSections.baseTest S))).hom.comp h
  have he := ConstantSectionsOn.ConstantSections.extend_const (⇑h') (ConstantSectionsOn.ConstantSections.baseTest S) c
  have hb : ConstantSectionsOn.ConstantSections.toBase (ConstantSectionsOn.ConstantSections.baseTest S) = 𝟙 (ConstantSectionsOn.ConstantSections.baseTest S) := Over.OverMorphism.ext rfl
  rw [hb, Category.id_comp] at he
  change (A.torsionSchemeYonedaIso N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest S))
    (ConstantSectionsOn.ConstantSections.extend h' (ConstantSectionsOn.ConstantSections.baseTest S) (LocallyConstant.const S c)) = h c
  exact (congrArg ((A.torsionSchemeYonedaIso N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest S))) he).trans
    (((A.torsionSchemeYonedaIso N).app (.op (ConstantSectionsOn.ConstantSections.baseTest S))).groupIsoToMulEquiv.apply_symm_apply _)

theorem torsionNatTrans_ext_on_constants
    {α β : HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ⟶ A.torsionFunctor N}
    (h : ∀ c : Frame.Labels.LevelCover.Coefficients g N,
      α.app (.op (ConstantSectionsOn.ConstantSections.baseTest S)) (LocallyConstant.const S c) =
        β.app (.op (ConstantSectionsOn.ConstantSections.baseTest S)) (LocallyConstant.const S c)) : α = β := by
  apply (cancel_mono (A.torsionSchemeYonedaIso N).inv).mp
  apply ConstantSectionsOn.ConstantSections.natTrans_ext_on_constants
  intro c
  exact congrArg ((A.torsionSchemeYonedaIso N).inv.app (.op (ConstantSectionsOn.ConstantSections.baseTest S))) (h c)

/-- The frame sections in the actual base-changed torsion kernel. -/
def frameAtBaseHom (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    Frame.Labels.LevelCover.Coefficients g N →* (A.pullback T.hom).torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest T.left) :=
  (A.torsionBaseChangeEquiv T.hom (ConstantSectionsOn.ConstantSections.baseTest T.left) N).symm.toMonoidHom.comp
    ((A.torsionPullback N (Frame.Labels.LevelCover.identityTestTo T)).comp (Frame.Labels.LevelCover.frameTorsionHom A T f))

/-- Universal frame map, defined before any local trivialization is chosen. -/
def frameLevelMap (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N T.left ⟶ (A.pullback T.hom).torsionFunctor N :=
  torsionSectionExtension (A.pullback T.hom) (frameAtBaseHom A T f)

theorem frameLevelMap_coefficients (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N)
    (c : Frame.Labels.LevelCover.Coefficients g N) :
    A.torsionBaseChangeEquiv T.hom (ConstantSectionsOn.ConstantSections.baseTest T.left) N
      ((frameLevelMap A T f).app (.op (ConstantSectionsOn.ConstantSections.baseTest T.left)) (LocallyConstant.const T.left c)) =
        A.torsionPullback N (Frame.Labels.LevelCover.identityTestTo T) (Frame.Labels.LevelCover.frameTorsionHom A T f c) := by
  have h := torsionSectionExtension_const (A.pullback T.hom) (frameAtBaseHom A T f) c
  exact (congrArg (A.torsionBaseChangeEquiv T.hom (ConstantSectionsOn.ConstantSections.baseTest T.left) N) h).trans
    ((A.torsionBaseChangeEquiv T.hom (ConstantSectionsOn.ConstantSections.baseTest T.left) N).apply_symm_apply _)

/-- On a split base the direct universal map is exactly the previously
constructed full-level isomorphism, by its values on coefficient vectors. -/
theorem frameLevelMap_eq_split [NeZero N] (α : A.FullLevel N)
    (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    frameLevelMap A T f = (Frame.Labels.LevelCover.fullLevelFromFrame A α T f).hom := by
  apply torsionNatTrans_ext_on_constants
  intro c
  apply (A.torsionBaseChangeEquiv T.hom (ConstantSectionsOn.ConstantSections.baseTest T.left) N).injective
  exact (frameLevelMap_coefficients A T f c).trans
    (Frame.Labels.LevelCover.fullLevelFromFrame_coefficients A α T f c).symm

theorem frameLevelMap_isIso_of_split [NeZero N] (α : A.FullLevel N)
    (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) : IsIso (frameLevelMap A T f) := by
  rw [frameLevelMap_eq_split A α T f]
  exact (Frame.Labels.LevelCover.fullLevelFromFrame A α T f).isIso_hom

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFrames.LevelCover
