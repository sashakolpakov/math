import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IsoRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.UniversalIso

/-! # Isomorphism Universal Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IsomorphismUniversalPoints

noncomputable section

/-! The universal bounded abelian isomorphism specializes to precisely the isomorphism classified by each parameter point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem boundedAbelianUniversalIso_point
    {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) {T : Over S} (c : T ⟶ IsoParameters.boundedAbelianIsoParameter A B j P) :
    Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (UniversalIso.boundedAbelianUniversalIso A B j P).hom =
      (IsoParameters.boundedAbelianIsoParameterPointEquiv A B j P T c).val.val.val := by
  have H := ConcreteCategory.congr_hom
    ((IsoRepresentation.boundedAbelianIsoClassifyingIso A B j P).hom.naturality c.op) (𝟙 (IsoParameters.boundedAbelianIsoParameter A B j P))
  have H' := congrArg (fun z : IsoParameters.BoundedFamilyAbelianIso A B j P T => z.val.val.val) H
  change (IsoParameters.boundedAbelianIsoParameterPointEquiv A B j P T (c ≫ 𝟙 _)).val.val.val =
    Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (UniversalIso.boundedAbelianUniversalIso A B j P).hom at H'
  exact H'.symm.trans (congrArg
    (fun d : T ⟶ IsoParameters.boundedAbelianIsoParameter A B j P => (IsoParameters.boundedAbelianIsoParameterPointEquiv A B j P T d).val.val.val)
    (Category.comp_id c))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IsomorphismUniversalPoints
