import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PoincareClassAdditivity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PicardFunctions
import OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection

/-! # Poincare Operators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PoincareOperators.RelativePoincareClasses

noncomputable section

/-! Actual Poincare classes are additive in either operator on a varying
noetherian family; the class on the dual factor detects the map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection.Construction

variable {S : Scheme.{0}} {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : HilbertConstruction.Dual.Data.DualAbelianData A)

def leftOperatorClass (d : D.abelian.scheme ⟶ D.abelian.scheme) :
    HilbertConstruction.Line.Bundles.LineBundle.IsoClass (D.abelian.scheme ⊗ A.scheme).left :=
  HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

def rightOperatorClass (u : A.scheme ⟶ A.scheme) :
    HilbertConstruction.Line.Bundles.LineBundle.IsoClass (D.abelian.scheme ⊗ A.scheme).left :=
  HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ u).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

theorem leftOperatorClass_eq_pair (d : D.abelian.scheme ⟶ D.abelian.scheme) :
    leftOperatorClass D d = PoincareClassAdditivity.RelativePoincareClasses.pairClass D (fst D.abelian.scheme A.scheme ≫ d)
      (snd D.abelian.scheme A.scheme) := by
  apply congrArg (fun v => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass v (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
  apply congrArg Over.Hom.left
  ext <;> simp only [tensorHom_fst, tensorHom_snd, lift_fst, lift_snd, Category.comp_id]

theorem rightOperatorClass_eq_pair (u : A.scheme ⟶ A.scheme) :
    rightOperatorClass D u = PoincareClassAdditivity.RelativePoincareClasses.pairClass D (fst D.abelian.scheme A.scheme)
      (snd D.abelian.scheme A.scheme ≫ u) := by
  apply congrArg (fun v => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass v (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
  apply congrArg Over.Hom.left
  ext <;> simp only [tensorHom_fst, tensorHom_snd, lift_fst, lift_snd, Category.comp_id]

theorem leftOperatorClass_injective : Function.Injective (leftOperatorClass D) := by
  intro d e h
  apply Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_injective D D.abelian.scheme
  change (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op D.abelian.scheme)
      (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ▷ A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) =
    (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op D.abelian.scheme)
      (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (e ▷ A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
  apply congrArg ((HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op D.abelian.scheme))
  change @Eq (HilbertConstruction.Line.Bundles.LineBundle.IsoClass (D.abelian.scheme ⊗ A.scheme).left) _ _
  convert h using 1
  simp only [leftOperatorClass, tensorHom_id]
  rfl

variable [IsNoetherian S]

local instance dualNoetherian : IsNoetherian D.abelian.scheme.left := by
  let : IsLocallyNoetherian D.abelian.scheme.left := LocallyOfFiniteType.isLocallyNoetherian D.abelian.scheme.hom
  let : CompactSpace D.abelian.scheme.left := QuasiCompact.compactSpace_of_compactSpace D.abelian.scheme.hom
  exact ⟨⟩

local instance productNoetherian : IsNoetherian (D.abelian.scheme ⊗ A.scheme).left :=
  PELModuli.IntegralModel.Relative.PicardFunctions.RelativePicardFunctions.product_isNoetherian A D.abelian.scheme

theorem leftOperatorClass_mul (d e : D.abelian.scheme ⟶ D.abelian.scheme) :
    leftOperatorClass D (d * e) = leftOperatorClass D d * leftOperatorClass D e := by
  rw [leftOperatorClass_eq_pair, leftOperatorClass_eq_pair, leftOperatorClass_eq_pair, MonObj.comp_mul]
  exact PoincareClassAdditivity.RelativePoincareClasses.pairClass_mul_left D _ _ _

theorem rightOperatorClass_mul (u v : A.scheme ⟶ A.scheme) :
    rightOperatorClass D (u * v) = rightOperatorClass D u * rightOperatorClass D v := by
  rw [rightOperatorClass_eq_pair, rightOperatorClass_eq_pair, rightOperatorClass_eq_pair, MonObj.comp_mul]
  exact PoincareClassAdditivity.RelativePoincareClasses.pairClass_mul_right D _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PoincareOperators.RelativePoincareClasses
