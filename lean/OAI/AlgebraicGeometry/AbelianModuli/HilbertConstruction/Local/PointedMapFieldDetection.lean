import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.BoundedPointedMapDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectiveCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FieldPullbackEquality

/-! # Pointed Map Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.PointedMapFieldDetection

noncomputable section

/-! Over a noetherian local ring, all pointed maps between abelian schemes with an embedded product are determined by their field-valued pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

theorem localPointedMap_eq_of_fieldPullbacks
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of R))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of R)))
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n)
    [IsClosedImmersion j.left] (f q : A.scheme ⟶ B.scheme)
    (hf : η[A.scheme] ≫ f = η[B.scheme]) (hq : η[A.scheme] ≫ q = η[B.scheme])
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ Spec (.of R)),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  obtain ⟨P, hP⟩ := ((MorphismGraphFamilies.morphismGraphFamily f).reembed j).exists_localFieldHilbertPolynomial
  have hpf : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P f := hP
  have hpq : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P q := hpf.of_fieldPullback_eq j P h
  exact Intrinsic.BoundedPointedMapDetection.nativeBoundedPointedMap_eq_of_fieldPullbacks A B j P f q hf hq hpf hpq h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.PointedMapFieldDetection
