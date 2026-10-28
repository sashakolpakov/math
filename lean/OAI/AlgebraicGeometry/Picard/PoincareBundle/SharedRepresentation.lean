import OAI.AlgebraicGeometry.Picard.PoincareBundle.HomogeneousComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FamilyIdentity
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData

/-! # Shared Representation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

noncomputable section

/-! The shared actual Poincare universal property supplies PoincareBundle's represented dual and universal class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.HomogeneousComparison OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)

/-- The given geometric dual represents the identical PoincareBundle homogeneous Picard sheaf. -/
def representation : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy D.abelian :=
  D.representable.ofIso ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso
    (HomogeneousComparison.homogeneousSheafIso A).symm)

/-- The representation comparison retains the same actual Picard section. -/
theorem representation_action {T : Over S} (x : T ⟶ D.abelian) :
    (HomogeneousComparison.homogeneousSheafIso A).hom.hom.app (op T) ((representation D).homEquiv x) =
      D.representable.homEquiv x := by
  change (HomogeneousComparison.homogeneousSheafIso A).hom.hom.app (op T)
    ((HomogeneousComparison.homogeneousSheafIso A).inv.hom.app (op T) (D.representable.homEquiv x)) = _
  exact congrArg (fun f => f (D.representable.homEquiv x))
    (congrArg (fun t => t.hom.app (op T)) (HomogeneousComparison.homogeneousSheafIso A).inv_hom_id)

/-- The homogeneous comparison commutes with the actual geometric sheafification maps. -/
theorem section_comparison {T : Over S}
    (q : (Homogeneous.homogeneousPresheaf A).obj (op T)) :
    (HomogeneousComparison.homogeneousSheafIso A).hom.hom.app (op T)
        ((toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T) q) =
      (toSheafify (Scheme.fppfTopology.over S) (Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).app (op T)
        ((HomogeneousComparison.homogeneousPresheafIso A).hom.app (op T) q) :=
  (congrArg (fun t => t.app (op T) q)
    (toSheafify_naturality (Scheme.fppfTopology.over S) (HomogeneousComparison.homogeneousPresheafIso A).hom)).symm

variable (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
  (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared D.poincare) (Vertical.ProductParameters.inputLeft D.abelian A))
  (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared D.poincare) (Vertical.ProductParameters.inputRight D.abelian A))
  (Line.Fibers.fiber (Line.Comparison.Bundle.fromShared D.poincare) (Vertical.ProductParameters.outputPoint D.abelian A)))
  (hβ : IsIso (Bilinear.BilinearPullback.toHom β))

/-- The original Poincare universal class is exactly the class used by PoincareBundle's map construction. -/
theorem universalClass : (representation D).homEquiv (𝟙 D.abelian) =
    Product.Map.sectionClass (Line.Comparison.Bundle.fromShared D.poincare) β hβ (𝟙 D.abelian) := by
  apply (ConcreteCategory.bijective_of_isIso ((HomogeneousComparison.homogeneousSheafIso A).hom.hom.app (op D.abelian))).1
  rw [representation_action, D.universalClass]
  change _ = (HomogeneousComparison.homogeneousSheafIso A).hom.hom.app (op D.abelian)
    ((toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op D.abelian)
      (Product.Map.homogeneousClass (Line.Comparison.Bundle.fromShared D.poincare) β hβ (𝟙 D.abelian)))
  rw [section_comparison]
  apply congrArg
    ((toSheafify (Scheme.fppfTopology.over S) (Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).app (op D.abelian))
  apply Subtype.ext
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare = Line.Comparison.Bundle.classEquiv (D.abelian ⊗ A).left
    (Vertical.Homogeneity.familyClass (Line.Comparison.Bundle.fromShared D.poincare) (𝟙 D.abelian))
  rw [FamilyIdentity.Family.familyClass_id]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation
