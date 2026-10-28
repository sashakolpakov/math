import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.MorphismPreservationParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.UniversalIso

/-! # Level Isomorphism Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.LevelIsomorphismParameters

noncomputable section

/-! Full-level preservation cuts out a specified closed quasi-projective locus in the bounded abelian-isomorphism parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N]
variable (A B : Abelian.Schemes.AbelianScheme g S) (l : A.FullLevel N) (k : B.FullLevel N)
variable (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

local instance boundedLevelIsoParameter_noetherian : IsNoetherian (IsoParameters.boundedAbelianIsoParameter A B j P).left :=
  (IsoParameters.boundedAbelianIsoParameterQuasiProjectivePresentation A B j P).noetherian

def boundedFullLevelIsoParameter : Over S :=
  Level.MorphismPreservationParameters.fullLevelMorphismPreservingParameter (IsoParameters.boundedAbelianIsoParameter A B j P)
    (A.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom)
    (B.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom)
    (l.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom)
    (k.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom) (UniversalIso.boundedAbelianUniversalIso A B j P).hom

def boundedFullLevelIsoParameterInclusion : boundedFullLevelIsoParameter A B l k j P ⟶ IsoParameters.boundedAbelianIsoParameter A B j P :=
  Level.MorphismPreservationParameters.fullLevelMorphismPreservingParameterInclusion _ _ _ _ _ _

instance boundedFullLevelIsoParameterInclusion_closed :
    IsClosedImmersion (boundedFullLevelIsoParameterInclusion A B l k j P).left :=
  Level.MorphismPreservationParameters.fullLevelMorphismPreservingParameterInclusion_closed _ _ _ _ _ _

def boundedFullLevelIsoParameterQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (boundedFullLevelIsoParameter A B l k j P) :=
  Level.MorphismPreservationParameters.fullLevelMorphismPreservingParameterQuasiProjectivePresentation _ _ _ _ _ _
    (IsoParameters.boundedAbelianIsoParameterQuasiProjectivePresentation A B j P)

def boundedFullLevelIsoParameterPointEquiv (T : Over S) :
    (T ⟶ boundedFullLevelIsoParameter A B l k j P) ≃
      Level.MorphismPreservationParameters.FullLevelMorphismPreservingPoint (IsoParameters.boundedAbelianIsoParameter A B j P)
        (A.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom)
        (B.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom)
        (l.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom)
        (k.pullback (IsoParameters.boundedAbelianIsoParameter A B j P).hom) (UniversalIso.boundedAbelianUniversalIso A B j P).hom T :=
  Level.MorphismPreservationParameters.fullLevelMorphismPreservingParameterPointEquiv _ _ _ _ _ _ T

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.LevelIsomorphismParameters
