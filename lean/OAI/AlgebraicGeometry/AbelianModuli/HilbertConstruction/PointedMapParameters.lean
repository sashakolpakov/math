import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedMonoidHomEquations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.MorphismEqualityParameters

/-! # Pointed Map Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMapParameters

noncomputable section

/-! Identity preservation by a universal family morphism is represented by a concrete closed parameter subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

local instance pointedParameterUnitProper {S : Scheme.{u}} : IsProper (𝟙_ (Over S)).hom :=
  inferInstanceAs (IsProper (𝟙 S))

local instance pointedParameterUnitFlat {S : Scheme.{u}} : Flat (𝟙_ (Over S)).hom :=
  inferInstanceAs (Flat (𝟙 S))

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left]
variable {X Y : Over M.left} [MonObj X] [MonObj Y] [IsSeparated Y.hom] (f : X ⟶ Y)

def pointedMapParameter : Over S := Proper.MorphismEqualityParameters.properMorphismEqualityParameter M (η[X] ≫ f) η[Y]

def pointedMapParameterInclusion : pointedMapParameter M f ⟶ M :=
  Proper.MorphismEqualityParameters.properMorphismEqualityParameterInclusion M (η[X] ≫ f) η[Y]

instance pointedMapParameterInclusion_closed : IsClosedImmersion (pointedMapParameterInclusion M f).left :=
  Proper.MorphismEqualityParameters.properMorphismEqualityParameterInclusion_closed M (η[X] ≫ f) η[Y]

def pointedMapParameterPointEquiv (T : Over S) :
    (T ⟶ pointedMapParameter M f) ≃ {c : T ⟶ M //
      η[(Over.pullback c.left).obj X] ≫ (Over.pullback c.left).map f = η[(Over.pullback c.left).obj Y]} :=
  (Proper.MorphismEqualityParameters.properMorphismEqualityParameterPointEquiv M (η[X] ≫ f) η[Y] T).trans
    { toFun := fun c => ⟨c.val, (MappedMonoidHomEquations.mappedMonoidHom_one_iff (Over.pullback c.val.left) f).mpr c.property⟩
      invFun := fun c => ⟨c.val, (MappedMonoidHomEquations.mappedMonoidHom_one_iff (Over.pullback c.val.left) f).mp c.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

theorem pointedMapParameter_universal :
    η[(Over.pullback (pointedMapParameterInclusion M f).left).obj X] ≫
      (Over.pullback (pointedMapParameterInclusion M f).left).map f =
        η[(Over.pullback (pointedMapParameterInclusion M f).left).obj Y] :=
  (MappedMonoidHomEquations.mappedMonoidHom_one_iff (Over.pullback (pointedMapParameterInclusion M f).left) f).mpr
    (Proper.MorphismEqualityParameters.properMorphismEqualityParameter_universal M (η[X] ≫ f) η[Y])

def pointedMapParameterQuasiProjectivePresentation [IsNoetherian S] (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation M) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (pointedMapParameter M f) :=
  Q.ofClosedImmersion (pointedMapParameterInclusion M f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMapParameters
