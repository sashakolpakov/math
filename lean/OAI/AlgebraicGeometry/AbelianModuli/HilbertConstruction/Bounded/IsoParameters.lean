import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomUniversalPoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ParameterQuasiProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts

/-! # Iso Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IsoParameters

noncomputable section

/-! Bounded isomorphisms between actual abelian families are represented on all test schemes by an open subscheme of the bounded homomorphism parameter. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

local instance boundedIsoPullbackProper {S T : Scheme.{u}} (c : T ⟶ S) (X : Over S) [IsProper X.hom] :
    IsProper ((Over.pullback c).obj X).hom := inferInstanceAs (IsProper (pullback.snd X.hom c))

local instance boundedIsoPullbackFlat {S T : Scheme.{u}} (c : T ⟶ S) (X : Over S) [Flat X.hom] :
    Flat ((Over.pullback c).obj X).hom := inferInstanceAs (Flat (pullback.snd X.hom c))

variable {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

def boundedAbelianIsoParameter : Over S :=
  IsomorphismOpenParameters.isomorphismOpenParameter (MonoidHomParameters.boundedFamilyMonoidHomParameter j P) (MonoidHomRepresentation.boundedFamilyMonoidHomUniversal j P).val.val

def boundedAbelianIsoParameterInclusion :
    boundedAbelianIsoParameter A B j P ⟶ MonoidHomParameters.boundedFamilyMonoidHomParameter j P :=
  Open.ParameterPoints.openParameterInclusion (MonoidHomParameters.boundedFamilyMonoidHomParameter j P)
    (HilbertConstruction.Over.IsomorphismOpen.overIsomorphismOpen (MonoidHomRepresentation.boundedFamilyMonoidHomUniversal j P).val.val)

instance boundedAbelianIsoParameterInclusion_open :
    IsOpenImmersion (boundedAbelianIsoParameterInclusion A B j P).left :=
  Open.ParameterPoints.openParameterInclusion_open _ _

def boundedAbelianIsoParameterQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (boundedAbelianIsoParameter A B j P) :=
  Proper.ParameterQuasiProjectivity.isomorphismOpenParameterQuasiProjectivePresentation (MonoidHomParameters.boundedFamilyMonoidHomParameter j P)
    (MonoidHomParameters.boundedFamilyMonoidHomParameterQuasiProjectivePresentation j P) (MonoidHomRepresentation.boundedFamilyMonoidHomUniversal j P).val.val

def BoundedFamilyAbelianIso (T : Over S) :=
  {f : MonoidHomParameters.BoundedFamilyMonoidHom j P T // IsIso f.val.val}

def boundedAbelianIsoParameterPointEquiv (T : Over S) :
    (T ⟶ boundedAbelianIsoParameter A B j P) ≃ BoundedFamilyAbelianIso A B j P T := by
  let M := MonoidHomParameters.boundedFamilyMonoidHomParameter j P
  have : IsNoetherian M.left := (MonoidHomParameters.boundedFamilyMonoidHomParameterQuasiProjectivePresentation j P).noetherian
  have : IsLocallyNoetherian ((Over.pullback M.hom).obj B.scheme).left :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd B.scheme.hom M.hom)
  exact (IsomorphismOpenParameters.isomorphismOpenParameterPointEquiv M (MonoidHomRepresentation.boundedFamilyMonoidHomUniversal j P).val.val T).trans
    ((MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P T).subtypeEquiv
      (fun c => HomUniversalPoint.boundedFamilyMonoidHomUniversal_pullback_isIso_iff j P c))

theorem boundedAbelianIsoParameterPointEquiv_val (T : Over S)
    (c : T ⟶ boundedAbelianIsoParameter A B j P) :
    (boundedAbelianIsoParameterPointEquiv A B j P T c).val =
      MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P T (c ≫ boundedAbelianIsoParameterInclusion A B j P) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IsoParameters
