import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualPullback
import OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousTensorPower
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusPairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.BaseChange

/-! # Dual Frobenius -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.DualFrobenius

noncomputable section

/-! Frobenius and dual Picard pullback, using the actual base-changed Poincare bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits hiding prodComparison prodComparison_fst prodComparison_snd
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S S' : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

theorem poincarePullbackOverMap_left_fst (f : S' ⟶ S) :
    (D.poincarePullbackOverMap f).left ≫ (fst D.abelian.scheme A.scheme).left =
      (fst (D.abelian.pullback f).scheme (A.pullback f).scheme).left ≫
        pullback.fst D.abelian.scheme.hom f := by
  have he := congrArg (fun z => z.left) (D.poincarePullbackOverMap_fst f)
  simpa only [Over.comp_left, Over.map_map_left, AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection,
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_apply, Over.id_left,
    Category.id_comp] using he

theorem poincarePullbackOverMap_left_snd (f : S' ⟶ S) :
    (D.poincarePullbackOverMap f).left ≫ (snd D.abelian.scheme A.scheme).left =
      (snd (D.abelian.pullback f).scheme (A.pullback f).scheme).left ≫
        pullback.fst A.scheme.hom f := by
  exact congrArg (fun z => z.left) (D.poincarePullbackOverMap_snd f)

variable (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)

theorem frobenius_poincare_product :
    (Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme ⊗ₘ
        Frobenius.Construction.relativeFrobenius p hp hS A.scheme).left ≫
      (D.poincarePullbackOverMap (Frobenius.Construction.absoluteFrobenius p hp S hS)).left =
    Frobenius.Construction.absoluteFrobenius p hp (D.abelian.scheme ⊗ A.scheme).left
      (Frobenius.Construction.prime_eq_zero_of_map p hS (D.abelian.scheme ⊗ A.scheme).hom) := by
  apply Over.tensorObj_ext
  · have he := poincarePullbackOverMap_left_fst D (Frobenius.Construction.absoluteFrobenius p hp S hS)
    change _ ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom = _ at he
    have ht := congrArg (fun z => z.left)
      (tensorHom_fst (Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme)
        (Frobenius.Construction.relativeFrobenius p hp hS A.scheme))
    change (Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme ⊗ₘ
      Frobenius.Construction.relativeFrobenius p hp hS A.scheme).left ≫
      (fst (D.abelian.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).scheme
        (A.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).scheme).left =
      (fst D.abelian.scheme A.scheme).left ≫
        (Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme).left at ht
    erw [Category.assoc, he, ← Category.assoc, ht, Category.assoc,
      Frobenius.Construction.relativeFrobenius_comp_fst]
    exact (Frobenius.Construction.absoluteFrobenius_naturality p hp _ _ (fst D.abelian.scheme A.scheme).left).symm
  · have he := poincarePullbackOverMap_left_snd D (Frobenius.Construction.absoluteFrobenius p hp S hS)
    change _ ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom = _ at he
    have ht := congrArg (fun z => z.left)
      (tensorHom_snd (Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme)
        (Frobenius.Construction.relativeFrobenius p hp hS A.scheme))
    change (Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme ⊗ₘ
      Frobenius.Construction.relativeFrobenius p hp hS A.scheme).left ≫
      (snd (D.abelian.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).scheme
        (A.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).scheme).left =
      (snd D.abelian.scheme A.scheme).left ≫
        (Frobenius.Construction.relativeFrobenius p hp hS A.scheme).left at ht
    erw [Category.assoc, he, ← Category.assoc, ht, Category.assoc,
      Frobenius.Construction.relativeFrobenius_comp_fst]
    exact (Frobenius.Construction.absoluteFrobenius_naturality p hp _ _ (snd D.abelian.scheme A.scheme).left).symm

/-- The simultaneous Frobenius pullback of the actual normalized Poincare bundle. -/
def frobeniusPoincarePullbackIso :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback
      (Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme ⊗ₘ
        Frobenius.Construction.relativeFrobenius p hp hS A.scheme).left
      (D.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).poincare).sheaf ≅
      (LineBundleTensor.Construction.tensorPowerLineBundle D.poincare p).sheaf :=
  (Scheme.Modules.pullbackComp
    (Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme ⊗ₘ
      Frobenius.Construction.relativeFrobenius p hp hS A.scheme).left
    (D.poincarePullbackOverMap (Frobenius.Construction.absoluteFrobenius p hp S hS)).left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (frobenius_poincare_product D p hp hS)).app D.poincare.sheaf ≪≫
    LineBundleTensor.Construction.frobeniusPullbackLineBundleIso p hp
      (Frobenius.Construction.prime_eq_zero_of_map p hS (D.abelian.scheme ⊗ A.scheme).hom) D.poincare

/-- Pullback on the actual dual induced by relative Frobenius. -/
def dualRelativeFrobenius :
    (D.abelian.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).scheme ⟶ D.abelian.scheme := by
  let f : A.scheme ⟶ (A.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).scheme :=
    Frobenius.Construction.relativeFrobenius p hp hS A.scheme
  have : IsMonHom f := Group.Construction.relativeFrobenius_isMonHom p hp hS A.scheme
  exact DualPullback.Construction.dualPicardPullback D (D.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)) f

theorem frobenius_dual_poincare :
    PoincareDetection.Construction.poincareClass D
      (Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme ≫ dualRelativeFrobenius D p hp hS) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op D.abelian.scheme)
      (LineBundleClasses.Construction.tensorPowerClass p (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) := by
  let f : A.scheme ⟶ (A.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).scheme :=
    Frobenius.Construction.relativeFrobenius p hp hS A.scheme
  have : IsMonHom f := Group.Construction.relativeFrobenius_isMonHom p hp hS A.scheme
  change PoincareDetection.Construction.poincareClass D (Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme ≫
    DualPullback.Construction.dualPicardPullback D (D.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)) f) = _
  erw [DualPullback.Construction.dualPicardPullback_poincare D (D.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)) f]
  dsimp only [PoincareDetection.Construction.poincareClass]
  rw [SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply]
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op D.abelian.scheme)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (D.abelian.scheme ◁ Frobenius.Construction.relativeFrobenius p hp hS A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme ▷
          (A.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).poincare))) = _
  apply congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op D.abelian.scheme))
  erw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left]
  erw [← tensorHom_def']
  exact Quotient.sound ⟨frobeniusPoincarePullbackIso D p hp hS⟩

/-- Frobenius followed by dual Frobenius represents the p-th tensor-power
operation on homogeneous line-bundle classes, over an arbitrary base. -/
theorem frobenius_dual_eq_picardTensorPower :
    Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme ≫ dualRelativeFrobenius D p hp hS =
      HomogeneousTensorPower.Construction.dualPicardTensorPower p hp hS D := by
  apply PoincareDetection.Construction.poincareClass_injective D D.abelian.scheme
  have ht := HomogeneousTensorPower.Construction.dualPicardTensorPower_poincare p hp hS D (𝟙 D.abelian.scheme)
  rw [Category.id_comp, PoincareDetection.Construction.poincareClass_id,
    SheafMaps.Construction.relativePicardTensorPower_toRelativePicard_apply] at ht
  exact (frobenius_dual_poincare D p hp hS).trans ht.symm

/-- The pullback composite of any map to the dual acts on Poincare classes
by actual tensor powers. This statement includes maps underlying polarizations. -/
theorem frobenius_pullback_dualMap (ell : A.scheme ⟶ D.abelian.scheme) :
    Frobenius.Construction.relativeFrobenius p hp hS A.scheme ≫
        (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map ell ≫
        dualRelativeFrobenius D p hp hS =
      ell ≫ HomogeneousTensorPower.Construction.dualPicardTensorPower p hp hS D := by
  erw [← Category.assoc, ← (Group.Construction.relativeFrobeniusNat p hp hS).naturality ell,
    Category.assoc, frobenius_dual_eq_picardTensorPower]
  rfl

theorem frobenius_pullback_dualMap_poincare (ell : A.scheme ⟶ D.abelian.scheme) :
    PoincareDetection.Construction.poincareClass D (Frobenius.Construction.relativeFrobenius p hp hS A.scheme ≫
        (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).map ell ≫
        dualRelativeFrobenius D p hp hS) =
      (SheafMaps.Construction.relativePicardTensorPower p hp hS A.scheme).hom.app (.op A.scheme)
        (PoincareDetection.Construction.poincareClass D ell) := by
  rw [frobenius_pullback_dualMap]
  exact HomogeneousTensorPower.Construction.dualPicardTensorPower_poincare p hp hS D ell

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.DualFrobenius
