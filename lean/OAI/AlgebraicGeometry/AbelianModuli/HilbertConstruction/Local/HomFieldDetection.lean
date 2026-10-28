import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectiveCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FieldPullbackEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.BoundedHomFieldDetection

/-! # Hom Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.HomFieldDetection

noncomputable section

/-! Over a noetherian local ring, field fibers detect all native homomorphisms between abelian schemes with an embedded product. The required graph polynomial is obtained from flatness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem localAbelianHom_eq_of_fieldPullbacks
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of R))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of R)))
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n)
    [IsClosedImmersion j.left] (f q : A.scheme ⟶ B.scheme) [IsMonHom f] [IsMonHom q]
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ Spec (.of R)),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  obtain ⟨P, hP⟩ := ((MorphismGraphFamilies.morphismGraphFamily f).reembed j).exists_localFieldHilbertPolynomial
  have hf : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P f := hP
  have hq : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P q := hf.of_fieldPullback_eq j P h
  exact Intrinsic.BoundedHomFieldDetection.nativeBoundedAbelianHom_eq_of_fieldPullbacks A B j P f q hf hq h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.HomFieldDetection
