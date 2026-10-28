import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.Family
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupIntrinsicUniversal

/-! # Group Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GroupParameters

noncomputable section

/-! The fixed-dimension Hilbert family supplies concrete projective embeddings for the bounded multiplication and inversion parameters, yielding an actual relative quasi-projective group-law parameter. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance hilbertGroupProductProper {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))

local instance hilbertGroupProductSmooth {S : Scheme.{u}} (X Y : Over S) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) (g : ℕ)

def fixedDimensionHilbertMultiplicationPresentation : Projective.ProjectivePresentations.ProjectivePresentation ((((Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme) ⊗ ((Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme)) ⊗ ((Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme)) :=
  ((Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).product (Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g)).product (Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g)

def fixedDimensionHilbertInversionPresentation : Projective.ProjectivePresentations.ProjectivePresentation (((Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme) ⊗ ((Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme)) := (Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).product (Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g)

variable (Pm Pi : Polynomial ℚ)

def fixedDimensionHilbertGroupRelativeParameter : Over (Parameters.fixedDimensionHilbertParameter S n P g).left :=
  Bounded.FamilyGroupParameter.boundedFamilyGroupParameter (fixedDimensionHilbertMultiplicationPresentation S n P g).embedding
    (fixedDimensionHilbertInversionPresentation S n P g).embedding Pm Pi (Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).quasiProjective

def fixedDimensionHilbertGroupRelativeQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi) :=
  Bounded.FamilyGroupParameter.boundedFamilyGroupParameterQuasiProjectivePresentation (fixedDimensionHilbertMultiplicationPresentation S n P g).embedding
    (fixedDimensionHilbertInversionPresentation S n P g).embedding Pm Pi (Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).quasiProjective

def fixedDimensionHilbertGroupUniversalFamily :
    Over (fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).left :=
  Bounded.FamilyGroupIntrinsicUniversal.boundedFamilyGroupNativeUniversalFamily (fixedDimensionHilbertMultiplicationPresentation S n P g).embedding
    (fixedDimensionHilbertInversionPresentation S n P g).embedding Pm Pi (Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).quasiProjective

@[instance_reducible] def fixedDimensionHilbertGroupUniversalGroupObj :
    GrpObj (fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi) :=
  Bounded.FamilyGroupIntrinsicUniversal.boundedFamilyGroupNativeUniversalGroupObj (fixedDimensionHilbertMultiplicationPresentation S n P g).embedding
    (fixedDimensionHilbertInversionPresentation S n P g).embedding Pm Pi (Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).quasiProjective

theorem fixedDimensionHilbertGroupUniversalGroupObj_comm :
    letI := fixedDimensionHilbertGroupUniversalGroupObj S n P g Pm Pi
    IsCommMonObj (fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi) :=
  Bounded.FamilyGroupIntrinsicUniversal.boundedFamilyGroupNativeUniversalGroupObj_comm (fixedDimensionHilbertMultiplicationPresentation S n P g).embedding
    (fixedDimensionHilbertInversionPresentation S n P g).embedding Pm Pi (Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).quasiProjective

theorem fixedDimensionHilbertGroupUniversalFamily_dimension :
    SmoothOfRelativeDimension g (fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
    (IsPullback.of_hasPullback ((Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme).hom (fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom)
    (Parameters.fixedDimensionHilbertUniversalFamily_dimension S n P g)

instance fixedDimensionHilbertGroupUniversalFamily_proper :
    IsProper (fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi).hom :=
  inferInstanceAs (IsProper (pullback.snd ((Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme).hom (fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GroupParameters
