import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.UniversalDualIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.MorphismEqualityParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Polarization Equality Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizationEqualityParameters

noncomputable section

/-! Polarization preservation cuts out a specified closed subscheme of the bounded abelian-isomorphism parameter, using its canonical universal dual isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g n : ℕ} {δ : Fin g → ℕ}
variable {A B : Abelian.Schemes.AbelianScheme g S} {D : Dual.Data.DualAbelianData A} {E : Dual.Data.DualAbelianData B}
variable (p : PolarizationData.Polarization D δ) (q : PolarizationData.Polarization E δ)
variable (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

def boundedPolarizationLeft :
    (A.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).scheme ⟶
      (E.abelian.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).scheme :=
  (p.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).isogeny.hom ≫
    (UniversalDualIsomorphism.boundedAbelianUniversalDualIso D E j P).hom

def boundedPolarizationRight :
    (A.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).scheme ⟶
      (E.abelian.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).scheme :=
  (UniversalIso.boundedAbelianUniversalIso A B j P).hom ≫
    (q.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom).isogeny.hom

local instance boundedIsoParameter_noetherian : IsNoetherian (IsoParameters.boundedAbelianIsoParameter A B j P).left :=
  (IsoParameters.boundedAbelianIsoParameterQuasiProjectivePresentation A B j P).noetherian

def boundedPolarizationIsoParameter : Over S :=
  Proper.MorphismEqualityParameters.properMorphismEqualityParameter (IsoParameters.boundedAbelianIsoParameter A B j P)
    (boundedPolarizationLeft p j P) (boundedPolarizationRight q j P)

def boundedPolarizationIsoParameterInclusion :
    boundedPolarizationIsoParameter p q j P ⟶ IsoParameters.boundedAbelianIsoParameter A B j P :=
  Proper.MorphismEqualityParameters.properMorphismEqualityParameterInclusion _ _ _

instance boundedPolarizationIsoParameterInclusion_closed :
    IsClosedImmersion (boundedPolarizationIsoParameterInclusion p q j P).left :=
  Proper.MorphismEqualityParameters.properMorphismEqualityParameterInclusion_closed _ _ _

def boundedPolarizationIsoParameterQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (boundedPolarizationIsoParameter p q j P) :=
  Proper.MorphismEqualityParameters.properMorphismEqualityParameterQuasiProjectivePresentation _ _ _
    (IsoParameters.boundedAbelianIsoParameterQuasiProjectivePresentation A B j P)

def boundedPolarizationIsoParameterPointEquiv (T : Over S) :
    (T ⟶ boundedPolarizationIsoParameter p q j P) ≃
      {c : T ⟶ IsoParameters.boundedAbelianIsoParameter A B j P //
        (Over.pullback c.left).map (boundedPolarizationLeft p j P) =
          (Over.pullback c.left).map (boundedPolarizationRight q j P)} :=
  Proper.MorphismEqualityParameters.properMorphismEqualityParameterPointEquiv _ _ _ T

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizationEqualityParameters
