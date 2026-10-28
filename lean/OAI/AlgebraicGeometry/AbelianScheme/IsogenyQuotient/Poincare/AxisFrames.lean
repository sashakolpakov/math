import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.OriginFrames

/-! # Axis Frames -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.AxisFrames.Construction

noncomputable section

/-! The actual normalization along the dual-zero axis gives the
horizontal unit frame, naturally on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelTrivialization

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

theorem poincareHorizontalUnit_factor {T : Over S} (c : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (hc : c ≫ fst D.abelian.scheme A.scheme = 1) :
    (c ≫ snd D.abelian.scheme A.scheme) ≫ (Picard.PoincareBundle.Poincare.KernelTrivialization.zeroSection (Z := D.abelian.scheme) (X := A.scheme)) = c := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Picard.PoincareBundle.Poincare.KernelTrivialization.zeroSection, Category.assoc, lift_fst, MonObj.comp_one] using hc.symm
  · simp only [Picard.PoincareBundle.Poincare.KernelTrivialization.zeroSection, Category.assoc, lift_snd, Category.comp_id]

def poincareHorizontalUnitFrame {T : Over S} (c : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (hc : c ≫ fst D.abelian.scheme A.scheme = 1) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) c :=
  Picard.PoincareBundle.GlobalPullbackFrame.atPoint (Picard.PoincareBundle.Poincare.KernelTrivialization.zeroSection (Z := D.abelian.scheme) (X := A.scheme)) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
    (Classical.choice D.normalizedAtDualZero).symm (c ≫ snd D.abelian.scheme A.scheme) c
    (poincareHorizontalUnit_factor D c hc)

theorem poincareHorizontalUnitFrame_natural {T U : Over S} (r : U ⟶ T)
    (c : T ⟶ D.abelian.scheme ⊗ A.scheme) (c' : U ⟶ D.abelian.scheme ⊗ A.scheme)
    (hc : c ≫ fst D.abelian.scheme A.scheme = 1) (hc' : c' ≫ fst D.abelian.scheme A.scheme = 1)
    (hr : r ≫ c = c') :
    Picard.PoincareBundle.Line.Fibers.pullSection (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) r c c' hr (poincareHorizontalUnitFrame D c hc).hom =
      (poincareHorizontalUnitFrame D c' hc').hom :=
  Picard.PoincareBundle.GlobalFrameNaturality.atPoint_section_natural
    (Picard.PoincareBundle.Poincare.KernelTrivialization.zeroSection (Z := D.abelian.scheme) (X := A.scheme)) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
    (Classical.choice D.normalizedAtDualZero).symm r (c ≫ snd D.abelian.scheme A.scheme) c
    (poincareHorizontalUnit_factor D c hc) (c' ≫ snd D.abelian.scheme A.scheme) c'
    (poincareHorizontalUnit_factor D c' hc')
    ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ snd D.abelian.scheme A.scheme) hr)) hr

theorem poincareHorizontalUnitFrame_zero (T : Over S) :
    poincareHorizontalUnitFrame D (1 : T ⟶ D.abelian.scheme ⊗ A.scheme)
      (MonObj.one_comp (fst D.abelian.scheme A.scheme)) = OriginFrames.Construction.poincareZeroFrame D T := by
  unfold poincareHorizontalUnitFrame OriginFrames.Construction.poincareZeroFrame
  simp only [MonObj.one_comp]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.AxisFrames.Construction
