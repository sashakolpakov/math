import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FamilyPower
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MonoidHomParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackMonoidIso

/-! # Constant Monoid Hom Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidHomParameters

noncomputable section

/-! All homomorphisms from a finite constant group into a proper projective group family are parameterized by a concrete closed subscheme of the finite-tuple parameter. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

local instance constantHomPullbackProper {S T : Scheme.{u}} (c : T ⟶ S) (X : Over S) [IsProper X.hom] :
    IsProper ((Over.pullback c).obj X).hom := inferInstanceAs (IsProper (pullback.snd X.hom c))

local instance constantHomPullbackFlat {S T : Scheme.{u}} (c : T ⟶ S) (X : Over S) [Flat X.hom] :
    Flat ((Over.pullback c).obj X).hom := inferInstanceAs (Flat (pullback.snd X.hom c))

local instance constantHomPullbackSeparated {S T : Scheme.{u}} (c : T ⟶ S) (X : Over S) [IsSeparated X.hom] :
    IsSeparated ((Over.pullback c).obj X).hom := inferInstanceAs (IsSeparated (pullback.snd X.hom c))

variable {S : Scheme.{u}} [IsNoetherian S] (A : Over S) [IsProper A.hom]
variable (I : Type u) [Fintype I] [MonObj A] [MonObj (ConstantScheme.Iff.constantScheme S I)]

def finiteConstantMonoidHomParameter : Over S :=
  Family.MonoidHomParameters.familyMonoidHomParameter (ConstantMorphismParameters.finiteConstantMorphismParameter A I) (ConstantMorphismParameters.finiteConstantUniversalMorphism A I)

def finiteConstantMonoidHomParameterInclusion :
    finiteConstantMonoidHomParameter A I ⟶ ConstantMorphismParameters.finiteConstantMorphismParameter A I :=
  Family.MonoidHomParameters.familyMonoidHomParameterInclusion _ (ConstantMorphismParameters.finiteConstantUniversalMorphism A I)

instance finiteConstantMonoidHomParameterInclusion_closed :
    IsClosedImmersion (finiteConstantMonoidHomParameterInclusion A I).left :=
  Family.MonoidHomParameters.familyMonoidHomParameterInclusion_closed _ (ConstantMorphismParameters.finiteConstantUniversalMorphism A I)

def FiniteConstantMonoidHom (T : Over S) :=
  {f : (Over.pullback T.hom).obj (ConstantScheme.Iff.constantScheme S I) ⟶ (Over.pullback T.hom).obj A // IsMonHom f}

omit [AlgebraicGeometry.IsNoetherian S] [IsProper A.hom] in
theorem finiteConstantUniversalMorphism_monHom_iff {T : Over S}
    (p : T ⟶ ConstantMorphismParameters.finiteConstantMorphismParameter A I) :
    IsMonHom (ConstantMorphismParameters.finiteConstantMorphismParameterPointEquiv A I T p) ↔
      IsMonHom ((Over.pullback p.left).map (ConstantMorphismParameters.finiteConstantUniversalMorphism A I)) := by
  rw [ConstantMorphismParameters.finiteConstantUniversalMorphism_point]
  exact ParameterPullbackMonoidIso.geometricFamilyMorphismBaseChange_isMonHom_iff p (ConstantMorphismParameters.finiteConstantUniversalMorphism A I)

def finiteConstantMonoidHomParameterPointEquiv (T : Over S) :
    (T ⟶ finiteConstantMonoidHomParameter A I) ≃ FiniteConstantMonoidHom A I T :=
  (Family.MonoidHomParameters.familyMonoidHomParameterPointEquiv _ (ConstantMorphismParameters.finiteConstantUniversalMorphism A I) T).trans
    ((ConstantMorphismParameters.finiteConstantMorphismParameterPointEquiv A I T).subtypeEquiv
      (fun p => (finiteConstantUniversalMorphism_monHom_iff A I p).symm))

theorem finiteConstantMonoidHomParameterPointEquiv_val (T : Over S)
    (p : T ⟶ finiteConstantMonoidHomParameter A I) :
    (finiteConstantMonoidHomParameterPointEquiv A I T p).val =
      ConstantMorphismParameters.finiteConstantMorphismParameterPointEquiv A I T (p ≫ finiteConstantMonoidHomParameterInclusion A I) := rfl

def finiteConstantMonoidHomParameterQuasiProjectivePresentation (P : Projective.ProjectivePresentations.ProjectivePresentation A)
    (x : 𝟙_ (Over S) ⟶ A) [IsClosedImmersion x.left] :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (finiteConstantMonoidHomParameter A I) :=
  Family.MonoidHomParameters.familyMonoidHomParameterQuasiProjectivePresentation _ (ConstantMorphismParameters.finiteConstantUniversalMorphism A I)
    (ConstantMorphismParameters.finiteConstantMorphismParameterProjective A I P x).quasiProjective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidHomParameters
