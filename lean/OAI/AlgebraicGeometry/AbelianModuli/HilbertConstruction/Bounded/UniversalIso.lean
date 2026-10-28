import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IsoParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BoundedHomUnramified

/-! # Universal Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.UniversalIso

noncomputable section

/-! The bounded abelian isomorphism parameter carries an actual universal group isomorphism and is formally unramified over its base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

def boundedAbelianUniversalIsoData : IsoParameters.BoundedFamilyAbelianIso A B j P (IsoParameters.boundedAbelianIsoParameter A B j P) :=
  IsoParameters.boundedAbelianIsoParameterPointEquiv A B j P _ (𝟙 _)

def boundedAbelianUniversalIso :
    (A.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).scheme ≅
      (B.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).scheme := by
  exact @asIso _ _ _ _ (boundedAbelianUniversalIsoData A B j P).val.val.val
    (boundedAbelianUniversalIsoData A B j P).property

theorem boundedAbelianUniversalIso_isMonHom : IsMonHom (boundedAbelianUniversalIso A B j P).hom :=
  (boundedAbelianUniversalIsoData A B j P).val.property

theorem boundedAbelianIsoParameter_formallyUnramified :
    FormallyUnramified (IsoParameters.boundedAbelianIsoParameter A B j P).hom := by
  let i := IsoParameters.boundedAbelianIsoParameterInclusion A B j P
  have hi : FormallyUnramified i.left := inferInstance
  have hM := Relative.BoundedHomUnramified.relativeBoundedAbelianHomParameter_formallyUnramified A B j P
  have hc : FormallyUnramified (i.left ≫ (MonoidHomParameters.boundedFamilyMonoidHomParameter j P).hom) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ hi hM
  exact (congrArg FormallyUnramified i.w).mp hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.UniversalIso
