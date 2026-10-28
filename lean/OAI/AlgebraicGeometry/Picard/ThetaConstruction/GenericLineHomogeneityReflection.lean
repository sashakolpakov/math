import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceFiberTriviality
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericFiberLineTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.SchemeProducts

/-! # Generic Line Homogeneity Reflection -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericLineHomogeneityReflection.Geometric

noncomputable section

/-! Homogeneity on the original generic residue fiber reflects to
universal homogeneity of a line family over an integral local base.
The normalized difference line is proved trivial on the whole square. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

private theorem inverse_one_product {M : Type*} [CommGroup M] :
    (1 : M)⁻¹ * 1⁻¹ = 1 := by
  simp only [inv_one, mul_one]

variable {S : Scheme.{0}} [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    [IsNoetherianRing Γ(S, ⊤)] [IsLocallyNoetherian S] [IsIntegral S]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

include P in
theorem difference_trivial_of_generic_homogeneous
    (hL : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (A.pullback (S.fromSpecResidueField (genericPoint S)))
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (A.scheme.hom.fiberι (genericPoint S))))) :
    Nonempty ((RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A.scheme ⊗ A.scheme).left) := by
  let B := A.product A
  let D := RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L
  let s : S ⟶ B.scheme.left :=
    (lift (1 : Over.mk (𝟙 S) ⟶ A.scheme) (1 : Over.mk (𝟙 S) ⟶ A.scheme)).left
  have hs : s ≫ B.scheme.hom = 𝟙 S :=
    (lift (1 : Over.mk (𝟙 S) ⟶ A.scheme) (1 : Over.mk (𝟙 S) ⟶ A.scheme)).w
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.pullback s) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass S := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).pullback
      (lift (1 : Over.mk (𝟙 S) ⟶ A.scheme) (1 : Over.mk (𝟙 S) ⟶ A.scheme)).left) = 1
    rw [DifferenceClassBaseChange.Geometric.relativeDifference_pair_class]
    simp only [RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass, one_mul, RelativeCubeClasses.Geometric.identityNormalizedLine_one_class, mul_one]
    exact @inverse_one_product (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (Over.mk (𝟙 S)).left)
      (Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup (Over.mk (𝟙 S)).left)
  let r : (Scheme.Modules.pullback s).obj D.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S :=
    Classical.choice (Quotient.exact hc)
  have hgeneric : Nonempty ((D.pullback (B.scheme.hom.fiberι (genericPoint S))).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (B.scheme.hom.fiber (genericPoint S))) :=
    DifferenceFiberTriviality.Geometric.difference_fieldFiber_trivial_of_homogeneous A L (S.fromSpecResidueField (genericPoint S)) hL
  exact GenericFiberLineTriviality.Geometric.genericFiber_line_trivial B.scheme.hom D (P.product P) s hs r hgeneric

include P in
theorem constantFamily_homogeneous_of_generic
    (hL : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (A.pullback (S.fromSpecResidueField (genericPoint S)))
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (A.scheme.hom.fiberι (genericPoint S)))))
    (U : Over S) :
    A.IsHomogeneousPicardClass U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd U A.scheme).left)) :=
  DifferenceTrivialityHomogeneity.Geometric.constantFamily_homogeneous_of_difference_trivial A L
    (Classical.choice (difference_trivial_of_generic_homogeneous A P L hL)) U

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericLineHomogeneityReflection.Geometric
