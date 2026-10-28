import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidHomRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphismOpenParameters

/-! # Constant Monoid Iso Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidIsoParameters

noncomputable section

/-! Isomorphisms from a finite constant group are parameterized by an actual open of the homomorphism parameter, preserving quasi-projectivity. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

local instance constantIsoPullbackProper {S T : Scheme.{u}} (c : T ⟶ S) (X : Over S) [IsProper X.hom] :
    IsProper ((Over.pullback c).obj X).hom := inferInstanceAs (IsProper (pullback.snd X.hom c))

local instance constantIsoPullbackFlat {S T : Scheme.{u}} (c : T ⟶ S) (X : Over S) [Flat X.hom] :
    Flat ((Over.pullback c).obj X).hom := inferInstanceAs (Flat (pullback.snd X.hom c))

variable {S : Scheme.{u}} [IsNoetherian S] (A : Over S) [IsProper A.hom]
variable (I : Type u) [Fintype I] [MonObj A] [MonObj (ConstantScheme.Iff.constantScheme S I)]

local instance constantIsoTargetNoetherian :
    IsLocallyNoetherian ((Over.pullback (ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I).hom).obj A).left :=
  (FamilyPower.properSource_noetherian (pullback.snd A.hom (ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I).hom)).toIsLocallyNoetherian

def finiteConstantMonoidIsoParameter : Over S :=
  IsomorphismOpenParameters.isomorphismOpenParameter (ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I) (ConstantMonoidHomRepresentation.finiteConstantMonoidHomUniversal A I).val

def finiteConstantMonoidIsoParameterInclusion :
    finiteConstantMonoidIsoParameter A I ⟶ ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I :=
  Open.ParameterPoints.openParameterInclusion _ (HilbertConstruction.Over.IsomorphismOpen.overIsomorphismOpen (ConstantMonoidHomRepresentation.finiteConstantMonoidHomUniversal A I).val)

instance finiteConstantMonoidIsoParameterInclusion_open :
    IsOpenImmersion (finiteConstantMonoidIsoParameterInclusion A I).left :=
  Open.ParameterPoints.openParameterInclusion_open _ (HilbertConstruction.Over.IsomorphismOpen.overIsomorphismOpen (ConstantMonoidHomRepresentation.finiteConstantMonoidHomUniversal A I).val)

def FiniteConstantMonoidIso (T : Over S) := {f : ConstantMonoidHomParameters.FiniteConstantMonoidHom A I T // IsIso f.val}

theorem finiteConstantMonoidHomUniversal_isIso_iff {T : Over S}
    (p : T ⟶ ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I) :
    IsIso (ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv A I T p).val ↔
      IsIso ((Over.pullback p.left).map (ConstantMonoidHomRepresentation.finiteConstantMonoidHomUniversal A I).val) := by
  rw [ConstantMonoidHomRepresentation.finiteConstantMonoidHomUniversal_point]
  exact Geometric.MorphismIsomorphisms.geometricFamilyMorphismBaseChange_isIso_iff p (ConstantMonoidHomRepresentation.finiteConstantMonoidHomUniversal A I).val

def finiteConstantMonoidIsoParameterPointEquiv (T : Over S) :
    (T ⟶ finiteConstantMonoidIsoParameter A I) ≃ FiniteConstantMonoidIso A I T :=
  (IsomorphismOpenParameters.isomorphismOpenParameterPointEquiv _ (ConstantMonoidHomRepresentation.finiteConstantMonoidHomUniversal A I).val T).trans
    ((ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv A I T).subtypeEquiv
      (fun p => (finiteConstantMonoidHomUniversal_isIso_iff A I p).symm))

theorem finiteConstantMonoidIsoParameterPointEquiv_val (T : Over S)
    (p : T ⟶ finiteConstantMonoidIsoParameter A I) :
    (finiteConstantMonoidIsoParameterPointEquiv A I T p).val =
      ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv A I T (p ≫ finiteConstantMonoidIsoParameterInclusion A I) := rfl

def finiteConstantMonoidIsoParameterQuasiProjectivePresentation (P : Projective.ProjectivePresentations.ProjectivePresentation A)
    (x : 𝟙_ (Over S) ⟶ A) [IsClosedImmersion x.left] :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (finiteConstantMonoidIsoParameter A I) :=
  (ConstantMonoidHomRepresentation.finiteConstantMonoidHomParameterProjective A I P x).quasiProjective.openParameter
    (HilbertConstruction.Over.IsomorphismOpen.overIsomorphismOpen (ConstantMonoidHomRepresentation.finiteConstantMonoidHomUniversal A I).val)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidIsoParameters
