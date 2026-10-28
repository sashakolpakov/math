import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map

/-! # Dual Poincare Bundle Representation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.DualPoincareBundleRepresentation.Construction

noncomputable section

/-! The original HilbertConstruction dual represents PoincareBundle's same homogeneous Picard
sheaf, and its original Poincare bundle retains the universal class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

def e45OriginalDualRepresentation :
    (Picard.PoincareBundle.Homogeneous.homogeneousSheaf A.scheme).obj.RepresentableBy D.abelian.scheme :=
  D.representable.ofIso ((sheafToPresheaf _ _).mapIso (HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso A).symm)

theorem e45OriginalDualRepresentation_homEquiv {T : Over S} (x : T ⟶ D.abelian.scheme) :
    (HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso A).hom.hom.app (.op T)
      ((e45OriginalDualRepresentation D).homEquiv x) = D.representable.homEquiv x := by
  exact (((sheafToPresheaf _ _).mapIso (HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso A)).app (.op T)).toEquiv.apply_symm_apply _

theorem e45OriginalPoincareUniversalClass
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
      (Picard.PoincareBundle.Line.Fibers.fiber (LineClassComparison.Construction.e33LineBundleToPoincareBundle D.poincare) (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft D.abelian.scheme A.scheme))
      (Picard.PoincareBundle.Line.Fibers.fiber (LineClassComparison.Construction.e33LineBundleToPoincareBundle D.poincare) (Picard.PoincareBundle.Vertical.ProductParameters.inputRight D.abelian.scheme A.scheme))
      (Picard.PoincareBundle.Line.Fibers.fiber (LineClassComparison.Construction.e33LineBundleToPoincareBundle D.poincare) (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint D.abelian.scheme A.scheme)))
    (hb : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom b)) :
    (e45OriginalDualRepresentation D).homEquiv (𝟙 D.abelian.scheme) =
      Picard.PoincareBundle.Product.Map.sectionClass (LineClassComparison.Construction.e33LineBundleToPoincareBundle D.poincare) b hb (𝟙 D.abelian.scheme) := by
  apply (((sheafToPresheaf _ _).mapIso (HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso A)).app
    (.op D.abelian.scheme)).toEquiv.injective
  change (HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso A).hom.hom.app (.op D.abelian.scheme)
    ((e45OriginalDualRepresentation D).homEquiv (𝟙 D.abelian.scheme)) = _
  rw [e45OriginalDualRepresentation_homEquiv]
  change D.representable.homEquiv (𝟙 D.abelian.scheme) =
    (HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso A).hom.hom.app (.op D.abelian.scheme)
      ((toSheafify (Scheme.fppfTopology.over S) (Picard.PoincareBundle.Homogeneous.homogeneousPresheaf A.scheme)).app
        (.op D.abelian.scheme) (Picard.PoincareBundle.Product.Map.homogeneousClass (LineClassComparison.Construction.e33LineBundleToPoincareBundle D.poincare) b hb (𝟙 _)))
  rw [HomogeneousPicardComparison.Construction.e45HomogeneousPicardSheafIso_toSheaf]
  refine D.universalClass.trans ?_
  apply congrArg ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op D.abelian.scheme))
  apply Subtype.ext
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare =
    LineClassComparison.Construction.e45LineClassEquiv _ (Picard.PoincareBundle.Line.Bundles.LineBundleClass.pullback (𝟙 D.abelian.scheme ⊗ₘ 𝟙 A.scheme).left
      (Picard.PoincareBundle.Line.Bundles.LineBundleClass.mk (LineClassComparison.Construction.e33LineBundleToPoincareBundle D.poincare)))
  rw [LineClassComparison.Construction.e45LineClassEquiv_pullback, LineClassComparison.Construction.e45LineClassEquiv_mk]
  have hid : (𝟙 D.abelian.scheme ⊗ₘ 𝟙 A.scheme).left = 𝟙 (D.abelian.scheme ⊗ A.scheme).left := by
    simp
  rw [hid, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.DualPoincareBundleRepresentation.Construction
