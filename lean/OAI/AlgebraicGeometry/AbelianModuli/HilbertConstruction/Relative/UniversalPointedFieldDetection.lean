import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalPointedFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.PointedBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomLocalRingDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFieldEquality

/-! # Universal Pointed Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.UniversalPointedFieldDetection

noncomputable section

/-! For fixed Noetherian abelian families with a projectively embedded product, every pointed map on every test scheme is detected by its field pullbacks. The graph bounds are constructed. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem relativeUniversalPointedMap_eq_of_fieldPullbacks
    {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (T : Over S) (f q : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme)
    (hf : η[(A.pullback T.hom).scheme] ≫ f = η[(B.pullback T.hom).scheme])
    (hq : η[(A.pullback T.hom).scheme] ≫ q = η[(B.pullback T.hom).scheme])
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ T.left),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  apply HilbertConstruction.Over.HomLocalRingDetection.overHom_eq_of_allLocalRingPullbacks
  intro R _ _ s
  let U : Over S := Over.mk (s ≫ T.hom)
  let c : U ⟶ T := Over.homMk s rfl
  apply (Geometric.MorphismEquality.geometricFamilyMorphismBaseChange_eq_iff c f q).mp
  exact LocalPointedFieldDetection.relativeLocalPointedMap_eq_of_fieldPullbacks A B j U.hom
    (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f) (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c q)
    (Geometric.PointedBaseChange.geometricFamilyMorphismBaseChange_preserves_unit c f hf)
    (Geometric.PointedBaseChange.geometricFamilyMorphismBaseChange_preserves_unit c q hq)
    (Geometric.MorphismFieldEquality.geometricFamilyMorphismBaseChange_fieldEquality c f q h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.UniversalPointedFieldDetection
