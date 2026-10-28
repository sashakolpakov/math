import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints

/-! # Product Over -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductOver.Constructions

noncomputable section

/-! The actual smooth strata and their fiber product as schemes over the
complex base, with genuine product projections and their universal property. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def regularOver (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFinitePresentation X.hom] : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (Geometric.SmoothStratum.smoothStratumToBase X.hom)

def regularOverInclusion (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFinitePresentation X.hom] : regularOver X ⟶ X :=
  Over.homMk (Geometric.SmoothStratum.smoothStratumι X.hom) rfl

instance regularOver_smooth (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFinitePresentation X.hom] :
    Smooth (regularOver X).hom := inferInstanceAs (Smooth (Geometric.SmoothStratum.smoothStratumToBase X.hom))

instance regularOverInclusion_open (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFinitePresentation X.hom] :
    IsOpenImmersion (regularOverInclusion X).left := inferInstanceAs (IsOpenImmersion (Geometric.SmoothStratum.smoothStratumι X.hom))

instance regularOver_integral (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFinitePresentation X.hom] [IsIntegral X.left] :
    IsIntegral (regularOver X).left := inferInstanceAs (IsIntegral (Geometric.SmoothStratum.smoothStratum X.hom))

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom]

def regularProductOver : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (pullback.fst (regularOver X).hom (regularOver Y).hom ≫ (regularOver X).hom)

def regularProductFst : regularProductOver X Y ⟶ regularOver X :=
  Over.homMk (pullback.fst (regularOver X).hom (regularOver Y).hom) rfl

def regularProductSnd : regularProductOver X Y ⟶ regularOver Y :=
  Over.homMk (pullback.snd (regularOver X).hom (regularOver Y).hom) pullback.condition.symm

def regularProductIsLimit : IsLimit (BinaryFan.mk (regularProductFst X Y) (regularProductSnd X Y)) :=
  (pullbackIsPullback (regularOver X).hom (regularOver Y).hom).pullbackConeEquivBinaryFanFunctor

instance regularProductOver_smooth : Smooth (regularProductOver X Y).hom :=
  Product.SupportTo.Constructions.SmoothOpen.schemeProduct_smooth (regularOver X) (regularOver Y)

instance regularProductOver_integral [IsIntegral X.left] [IsIntegral Y.left] :
    IsIntegral (regularProductOver X Y).left :=
  Scheme.ProductIntegral.Constructions.schemeProduct_isIntegral (regularOver X) (regularOver Y)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductOver.Constructions
