import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectiveGluing
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.DiagramGluing
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.CompactificationNaturality

/-! # Compactification Diagram -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.CompactificationDiagram.BundleCycles

noncomputable section

/-! The distinguished affine embeddings form an actual natural
transformation from the conormal spectrum diagram to its projective diagram. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def conormalCompactificationDiagram :
    (DiagramGluing.BundleCycles.conormalSymmetricGlueData I).functor ⟶ (ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).functor where
  app U := Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent
  naturality {_U _V} i := Symmetric.CompactificationNaturality.BundleCycles.symmetricAffineCompactification_naturality _ _ (RestrictionSpan.BundleCycles.conormalRestriction_span I i)

theorem conormalCompactificationDiagram_over :
    conormalCompactificationDiagram I ≫ (ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).natTrans =
      (DiagramGluing.BundleCycles.conormalSymmetricGlueData I).natTrans := by
  apply NatTrans.ext
  funext U
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  let a := CommRingCat.ofHom (algebraMap (Γ(X, U.1) ⧸ I.ideal U)
    (SymmetricAlgebra (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent))
  change Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent ≫
    (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase (Γ(X, U.1) ⧸ I.ideal U)
      ((Γ(X, U.1) ⧸ I.ideal U) × (I.ideal U).Cotangent) ≫
        (Spec.map q ≫ U.2.isoSpec.inv)) =
    Spec.map ((SymmetricDiagram.BundleCycles.conormalSymmetricDiagramMap I).app (.op U)) ≫ U.2.isoSpec.inv
  rw [← Category.assoc, Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification_over, ← Category.assoc, ← Spec.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.CompactificationDiagram.BundleCycles
