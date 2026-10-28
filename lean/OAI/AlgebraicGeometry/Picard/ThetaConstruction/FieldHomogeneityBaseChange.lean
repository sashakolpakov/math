import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceFiberHomogeneity
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldFrameReflection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.SchemeProducts

/-! # Field Homogeneity Base Change -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldHomogeneityBaseChange.Geometric

noncomputable section

/-! Homogeneity of an actual field line is preserved and reflected
by every field extension. Reflection uses the actual normalized frame
scheme of the difference line on the original abelian square. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

private theorem field_inverse_one_product {M : Type*} [CommGroup M] :
    (1 : M)⁻¹ * 1⁻¹ = 1 := by
  simp only [inv_one, mul_one]

variable {k K : Type} [Field k] [Field K] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (b : Spec (.of K) ⟶ Spec (.of k))

theorem homogeneousLine_baseChange
    (hL : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (A.pullback b)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst A.scheme.hom b))) := by
  obtain ⟨e⟩ := (DifferenceTrivialityHomogeneity.Geometric.difference_trivial_iff_homogeneous_line A L).mpr hL
  exact DifferenceFiberHomogeneity.Geometric.homogeneous_fieldFiber_of_difference_trivial A L b
    ((Scheme.Modules.pullback (pullback.fst (A.scheme ⊗ A.scheme).hom b)).mapIso e ≪≫
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (pullback.fst (A.scheme ⊗ A.scheme).hom b))

theorem homogeneousLine_of_baseChange (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (hL : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (A.pullback b)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst A.scheme.hom b)))) :
    AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
  let B := A.product A
  let D := RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L
  let s : Spec (.of k) ⟶ B.scheme.left :=
    (lift (1 : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme)
      (1 : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme)).left
  have hs : s ≫ B.scheme.hom = 𝟙 (Spec (.of k)) :=
    (lift (1 : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme)
      (1 : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme)).w
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.pullback s) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Spec (.of k)) := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).pullback
      (lift (1 : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme)
        (1 : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme)).left) = 1
    rw [DifferenceClassBaseChange.Geometric.relativeDifference_pair_class]
    simp only [RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass, one_mul, RelativeCubeClasses.Geometric.identityNormalizedLine_one_class, mul_one]
    exact @field_inverse_one_product (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (Over.mk (𝟙 (Spec (.of k)))).left)
      (Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup (Over.mk (𝟙 (Spec (.of k)))).left)
  let r : (Scheme.Modules.pullback s).obj D.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k)) :=
    Classical.choice (Quotient.exact hc)
  obtain ⟨e⟩ := DifferenceFiberTriviality.Geometric.difference_fieldFiber_trivial_of_homogeneous A L b hL
  let : IsProper (A.scheme ⊗ A.scheme).hom := B.proper
  let : Smooth (A.scheme ⊗ A.scheme).hom := by
    let : SmoothOfRelativeDimension (g + g) (A.scheme ⊗ A.scheme).hom := B.smoothDimension
    exact SmoothOfRelativeDimension.smooth (g + g) _
  let : GeometricallyConnected (A.scheme ⊗ A.scheme).hom := B.connected
  have hD := FieldFrameReflection.Geometric.field_line_trivial_of_cartesian_trivial (P.product P) s hs D r
    (pullback.fst B.scheme.hom b) (pullback.snd B.scheme.hom b) b
    (IsPullback.of_hasPullback B.scheme.hom b) e
  exact (DifferenceTrivialityHomogeneity.Geometric.difference_trivial_iff_homogeneous_line A L).mp hD

theorem homogeneousLine_baseChange_iff (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme) :
    AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (A.pullback b)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst A.scheme.hom b))) ↔
        AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) :=
  ⟨homogeneousLine_of_baseChange A L b P, homogeneousLine_baseChange A L b⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldHomogeneityBaseChange.Geometric
