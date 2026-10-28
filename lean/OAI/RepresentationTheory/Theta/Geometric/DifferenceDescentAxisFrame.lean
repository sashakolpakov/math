import OAI.RepresentationTheory.Theta.Geometric.DifferenceAxisTransport
import OAI.RepresentationTheory.Theta.Geometric.DescendedDifferenceBundle

/-! # Difference Descent Axis Frame -/

namespace OAI.RepresentationTheory.Theta.Geometric.DifferenceDescentAxisFrame

noncomputable section

/-! The underlying ordinary scheme descent datum preserves the native
axis frame, including for nonreduced test schemes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization
attribute [local instance] AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (labels : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : ∀ a : p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme a.val).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

def axisCoverMap {T : Scheme} (q : T ⟶ B.scheme.left) (x : T ⟶ A.scheme.left)
    (hx : x ≫ p.hom.left = q) :
    AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent.testObject (q ≫ (lift (𝟙 B.scheme) (1 : B.scheme ⟶ A.scheme)).left) ⟶
      A.scheme :=
  Over.homMk x (by
    change x ≫ A.scheme.hom =
      (q ≫ (lift (𝟙 B.scheme) (1 : B.scheme ⟶ A.scheme)).left) ≫ (B.scheme ⊗ A.scheme).hom
    rw [Category.assoc, Over.w, ← hx, Category.assoc, Over.w])

theorem differenceDescentDatum_axis {T : Scheme} (q : T ⟶ B.scheme.left)
    (x y : T ⟶ A.scheme.left) (hx : x ≫ p.hom.left = q) (hy : y ≫ p.hom.left = q) :
    (DescendedDifferenceBundle.differenceDescentDatum p labels L hL e).hom (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      (q ≫ (lift (𝟙 B.scheme) (1 : B.scheme ⟶ A.scheme)).left)
      (x ≫ (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left)
      (y ≫ (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left)
      (by rw [Category.assoc, ← Over.comp_left, DifferenceAxisTransport.productIsogeny_firstZeroSlice,
        Over.comp_left, ← Category.assoc, hx])
      (by rw [Category.assoc, ← Over.comp_left, DifferenceAxisTransport.productIsogeny_firstZeroSlice,
        Over.comp_left, ← Category.assoc, hy]) ≫
      (FactoredPullbackFrames.factoredPullbackFrame y (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left e).hom =
        (FactoredPullbackFrames.factoredPullbackFrame x (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left e).hom := by
  let v := axisCoverMap p q x hx
  let w := axisCoverMap p q y hy
  let i := lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)
  have hvw : (v ≫ i) ≫ (p.hom ⊗ₘ 𝟙 A.scheme) =
      (w ≫ i) ≫ (p.hom ⊗ₘ 𝟙 A.scheme) := by
    apply Over.OverMorphism.ext
    change (x ≫ i.left) ≫ (p.hom ⊗ₘ 𝟙 A.scheme).left =
      (y ≫ i.left) ≫ (p.hom ⊗ₘ 𝟙 A.scheme).left
    have h := congrArg Over.Hom.left (DifferenceAxisTransport.productIsogeny_firstZeroSlice p)
    change i.left ≫ (p.hom ⊗ₘ 𝟙 A.scheme).left =
      p.hom.left ≫ (lift (𝟙 B.scheme) (1 : B.scheme ⟶ A.scheme)).left at h
    rw [Category.assoc, Category.assoc, h, ← Category.assoc, ← Category.assoc, hx, hy]
  exact DifferenceAxisTransport.differenceKernelTransportIso_axis p labels L hL e v w
    (AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair.pointDifference (p.hom ⊗ₘ 𝟙 A.scheme) (v ≫ i) (w ≫ i) hvw)
    (AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization.difference_translates (p.hom ⊗ₘ 𝟙 A.scheme) (v ≫ i) (w ≫ i) hvw)

end

end OAI.RepresentationTheory.Theta.Geometric.DifferenceDescentAxisFrame
