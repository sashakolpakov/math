import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledTensorPower
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusPairing
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualBaseChange

/-! # Unbundled Dual Frobenius -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualFrobenius

noncomputable section

/-! Frobenius pullback on the actual universal Poincare bundle, without
requiring a constant relative dimension on the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits hiding prodComparison prodComparison_fst prodComparison_snd
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction.UnbundledPicard

universe u
variable {S S' : Scheme.{u}} {A : Over S} [GrpObj A] (D : UnbundledDualData.Construction.UnbundledPicard.DualData A)

theorem poincarePullbackOverMap_left_fst (f : S' ⟶ S) :
    (D.poincarePullbackOverMap f).left ≫ (fst D.abelian A).left =
      (fst (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).left ≫
        pullback.fst D.abelian.hom f := by
  have he := congrArg (fun z => z.left) (D.poincarePullbackOverMap_fst f)
  simpa only [Over.comp_left, Over.map_map_left, UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection,
    UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv_apply, Over.id_left,
    Category.id_comp] using he

theorem poincarePullbackOverMap_left_snd (f : S' ⟶ S) :
    (D.poincarePullbackOverMap f).left ≫ (snd D.abelian A).left =
      (snd (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).left ≫
        pullback.fst A.hom f := by
  exact congrArg (fun z => z.left) (D.poincarePullbackOverMap_snd f)

variable (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)

theorem frobenius_poincare_product :
    (Frobenius.Construction.relativeFrobenius p hp hS D.abelian ⊗ₘ
        Frobenius.Construction.relativeFrobenius p hp hS A).left ≫
      (D.poincarePullbackOverMap (Frobenius.Construction.absoluteFrobenius p hp S hS)).left =
    Frobenius.Construction.absoluteFrobenius p hp (D.abelian ⊗ A).left
      (Frobenius.Construction.prime_eq_zero_of_map p hS (D.abelian ⊗ A).hom) := by
  apply Over.tensorObj_ext
  · have he := poincarePullbackOverMap_left_fst D (Frobenius.Construction.absoluteFrobenius p hp S hS)
    change _ ≫ pullback.fst D.abelian.hom A.hom = _ at he
    have ht := congrArg (fun z => z.left)
      (tensorHom_fst (Frobenius.Construction.relativeFrobenius p hp hS D.abelian)
        (Frobenius.Construction.relativeFrobenius p hp hS A))
    change (Frobenius.Construction.relativeFrobenius p hp hS D.abelian ⊗ₘ
      Frobenius.Construction.relativeFrobenius p hp hS A).left ≫
      (fst (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian (Frobenius.Construction.absoluteFrobenius p hp S hS))
        (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A (Frobenius.Construction.absoluteFrobenius p hp S hS))).left =
      (fst D.abelian A).left ≫
        (Frobenius.Construction.relativeFrobenius p hp hS D.abelian).left at ht
    erw [Category.assoc, he, ← Category.assoc, ht, Category.assoc,
      Frobenius.Construction.relativeFrobenius_comp_fst]
    exact (Frobenius.Construction.absoluteFrobenius_naturality p hp _ _ (fst D.abelian A).left).symm
  · have he := poincarePullbackOverMap_left_snd D (Frobenius.Construction.absoluteFrobenius p hp S hS)
    change _ ≫ pullback.snd D.abelian.hom A.hom = _ at he
    have ht := congrArg (fun z => z.left)
      (tensorHom_snd (Frobenius.Construction.relativeFrobenius p hp hS D.abelian)
        (Frobenius.Construction.relativeFrobenius p hp hS A))
    change (Frobenius.Construction.relativeFrobenius p hp hS D.abelian ⊗ₘ
      Frobenius.Construction.relativeFrobenius p hp hS A).left ≫
      (snd (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian (Frobenius.Construction.absoluteFrobenius p hp S hS))
        (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A (Frobenius.Construction.absoluteFrobenius p hp S hS))).left =
      (snd D.abelian A).left ≫
        (Frobenius.Construction.relativeFrobenius p hp hS A).left at ht
    erw [Category.assoc, he, ← Category.assoc, ht, Category.assoc,
      Frobenius.Construction.relativeFrobenius_comp_fst]
    exact (Frobenius.Construction.absoluteFrobenius_naturality p hp _ _ (snd D.abelian A).left).symm

/-- The simultaneous Frobenius pullback of the actual normalized Poincare bundle. -/
def frobeniusPoincarePullbackIso :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback
      (Frobenius.Construction.relativeFrobenius p hp hS D.abelian ⊗ₘ
        Frobenius.Construction.relativeFrobenius p hp hS A).left
      (D.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).poincare).sheaf ≅
      (LineBundleTensor.Construction.tensorPowerLineBundle D.poincare p).sheaf :=
  (Scheme.Modules.pullbackComp
    (Frobenius.Construction.relativeFrobenius p hp hS D.abelian ⊗ₘ
      Frobenius.Construction.relativeFrobenius p hp hS A).left
    (D.poincarePullbackOverMap (Frobenius.Construction.absoluteFrobenius p hp S hS)).left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (frobenius_poincare_product D p hp hS)).app D.poincare.sheaf ≪≫
    LineBundleTensor.Construction.frobeniusPullbackLineBundleIso p hp
      (Frobenius.Construction.prime_eq_zero_of_map p hS (D.abelian ⊗ A).hom) D.poincare

/-- Pullback on the actual dual induced by relative Frobenius. -/
def dualRelativeFrobenius :
    (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian (Frobenius.Construction.absoluteFrobenius p hp S hS)) ⟶ D.abelian := by
  let f : A ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A (Frobenius.Construction.absoluteFrobenius p hp S hS)) :=
    Frobenius.Construction.relativeFrobenius p hp hS A
  have : IsMonHom f := Group.Construction.relativeFrobenius_isMonHom p hp hS A
  exact UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D (D.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)) f

theorem frobenius_dual_poincare :
    UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D
      (Frobenius.Construction.relativeFrobenius p hp hS D.abelian ≫ dualRelativeFrobenius D p hp hS) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op D.abelian)
      (LineBundleClasses.Construction.tensorPowerClass p (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) := by
  let f : A ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A (Frobenius.Construction.absoluteFrobenius p hp S hS)) :=
    Frobenius.Construction.relativeFrobenius p hp hS A
  have : IsMonHom f := Group.Construction.relativeFrobenius_isMonHom p hp hS A
  change UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D (Frobenius.Construction.relativeFrobenius p hp hS D.abelian ≫
    UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D (D.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)) f) = _
  erw [UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback_poincare D (D.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)) f]
  dsimp only [UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass]
  rw [SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply]
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op D.abelian)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (D.abelian ◁ Frobenius.Construction.relativeFrobenius p hp hS A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (Frobenius.Construction.relativeFrobenius p hp hS D.abelian ▷
          (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A (Frobenius.Construction.absoluteFrobenius p hp S hS))).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).poincare))) = _
  apply congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op D.abelian))
  erw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left]
  erw [← tensorHom_def']
  exact Quotient.sound ⟨frobeniusPoincarePullbackIso D p hp hS⟩

/-- Frobenius followed by dual Frobenius represents the p-th tensor-power
operation on homogeneous line-bundle classes, over an arbitrary base. -/
theorem frobenius_dual_eq_picardTensorPower :
    Frobenius.Construction.relativeFrobenius p hp hS D.abelian ≫ dualRelativeFrobenius D p hp hS =
      UnbundledTensorPower.Construction.UnbundledPicard.dualPicardTensorPower p hp hS D := by
  apply UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_injective D D.abelian
  have ht := UnbundledTensorPower.Construction.UnbundledPicard.dualPicardTensorPower_poincare p hp hS D (𝟙 D.abelian)
  rw [Category.id_comp, UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_id,
    SheafMaps.Construction.relativePicardTensorPower_toRelativePicard_apply] at ht
  exact (frobenius_dual_poincare D p hp hS).trans ht.symm

/-- The pullback composite of any map to the dual acts on Poincare classes
by actual tensor powers. This statement includes maps underlying polarizations. -/
theorem frobenius_pullback_dualMap (ell : A ⟶ D.abelian) :
    Frobenius.Construction.relativeFrobenius p hp hS A ≫
        (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map ell ≫
        dualRelativeFrobenius D p hp hS =
      ell ≫ UnbundledTensorPower.Construction.UnbundledPicard.dualPicardTensorPower p hp hS D := by
  erw [← Category.assoc, ← (Group.Construction.relativeFrobeniusNat p hp hS).naturality ell,
    Category.assoc, frobenius_dual_eq_picardTensorPower]
  rfl

theorem frobenius_pullback_dualMap_poincare (ell : A ⟶ D.abelian) :
    UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D (Frobenius.Construction.relativeFrobenius p hp hS A ≫
        (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map ell ≫
        dualRelativeFrobenius D p hp hS) =
      (SheafMaps.Construction.relativePicardTensorPower p hp hS A).hom.app (.op A)
        (UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D ell) := by
  rw [frobenius_pullback_dualMap]
  exact UnbundledTensorPower.Construction.UnbundledPicard.dualPicardTensorPower_poincare p hp hS D ell

end Construction.UnbundledPicard

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualFrobenius
