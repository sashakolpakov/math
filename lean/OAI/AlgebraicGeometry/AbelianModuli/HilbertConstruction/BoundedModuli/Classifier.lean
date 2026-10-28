import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.IsomorphismFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IsomorphismUniversalPoints

/-! # Classifier -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli

noncomputable section

/-! Every bounded complete moduli isomorphism has its canonical point in the bounded abelian-isomorphism parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ) {T : Over S} (e : IsomorphismFunctor.BoundedFamilyLevelIso A B j P T)

def IsomorphismFunctor.BoundedFamilyLevelIso.abelianData : Bounded.IsoParameters.BoundedFamilyAbelianIso A.abelian B.abelian j P T :=
  ⟨⟨⟨e.val.abelian.hom, e.property⟩, e.val.abelianGroup⟩, inferInstanceAs (IsIso e.val.abelian.hom)⟩

def IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier : T ⟶ Bounded.IsoParameters.boundedAbelianIsoParameter A.abelian B.abelian j P :=
  (Bounded.IsoParameters.boundedAbelianIsoParameterPointEquiv A.abelian B.abelian j P T).symm (IsomorphismFunctor.BoundedFamilyLevelIso.abelianData A B j P e)

theorem IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier_point :
    (Bounded.IsoParameters.boundedAbelianIsoParameterPointEquiv A.abelian B.abelian j P T
      (IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e)).val.val.val = e.val.abelian.hom :=
  congrArg (fun z : Bounded.IsoParameters.BoundedFamilyAbelianIso A.abelian B.abelian j P T => z.val.val.val)
    ((Bounded.IsoParameters.boundedAbelianIsoParameterPointEquiv A.abelian B.abelian j P T).apply_symm_apply
      (IsomorphismFunctor.BoundedFamilyLevelIso.abelianData A B j P e))

theorem IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier_recovers :
    e.val.abelian.hom = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e)
      (Bounded.UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom := by
  have H := (Bounded.IsoParameters.boundedAbelianIsoParameterPointEquiv A.abelian B.abelian j P T).apply_symm_apply (IsomorphismFunctor.BoundedFamilyLevelIso.abelianData A B j P e)
  have H' := congrArg (fun z : Bounded.IsoParameters.BoundedFamilyAbelianIso A.abelian B.abelian j P T => z.val.val.val) H
  exact ((Bounded.IsomorphismUniversalPoints.boundedAbelianUniversalIso_point A.abelian B.abelian j P (IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e)).trans H').symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli
