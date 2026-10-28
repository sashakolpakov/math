import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.OpenEquality
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # Ideal Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdealDescent

noncomputable section

/-! Compatible ideal sheaves on a locally directed open cover give actual scheme gluing data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (C : X.OpenCover) [Category C.I₀] [C.LocallyDirected]

/-- Local ideal sheaves with equality under every transition of a directed open cover. -/
structure IdealDescentData where
  ideal : ∀ i, (C.X i).IdealSheafData
  compatible : ∀ {i j} (f : i ⟶ j), (ideal j).comap (C.trans f) = ideal i

namespace IdealDescentData

variable {C} (D : IdealDescentData C)

/-- A cover transition restricts to the canonical closed subschemes. -/
def transition {i j : C.I₀} (f : i ⟶ j) : (D.ideal i).subscheme ⟶ (D.ideal j).subscheme :=
  Scheme.IdealSheafData.subschemeMap (D.ideal i) (D.ideal j) (C.trans f)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr (D.compatible f).le)

@[reassoc (attr := simp)]
theorem transition_inclusion {i j : C.I₀} (f : i ⟶ j) :
    D.transition f ≫ (D.ideal j).subschemeι = (D.ideal i).subschemeι ≫ C.trans f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The transition square is Cartesian because its ideals agree by pullback. -/
theorem transition_isPullback {i j : C.I₀} (f : i ⟶ j) :
    IsPullback (D.transition f) (D.ideal i).subschemeι (D.ideal j).subschemeι (C.trans f) := by
  apply IsPullback.flip
  apply isPullback_of_isClosedImmersion
  · exact (D.transition_inclusion f).symm
  · rw [(D.ideal j).ker_subschemeι, (D.ideal i).ker_subschemeι]
    exact D.compatible f

/-- The local closed subschemes and their actual transition maps form a diagram. -/
def schemeFunctor : C.I₀ ⥤ Scheme.{u} where
  obj i := (D.ideal i).subscheme
  map f := D.transition f
  map_id i := by
    apply (cancel_mono (D.ideal i).subschemeι).mp
    simp only [IdealDescentData.transition_inclusion, Scheme.Cover.trans_id, Category.comp_id, Category.id_comp]
  map_comp f h := by
    apply (cancel_mono (D.ideal _).subschemeι).mp
    simp only [IdealDescentData.transition_inclusion, Category.assoc, transition_inclusion_assoc,
      Scheme.Cover.trans_comp]

/-- Compatible ideals supply the equifibered diagram used by relative scheme gluing. -/
def relativeGluingData : C.RelativeGluingData where
  functor := D.schemeFunctor
  natTrans :=
    { app i := (D.ideal i).subschemeι
      naturality _ _ f := D.transition_inclusion f }
  equifibered _ _ f := D.transition_isPullback f

end IdealDescentData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdealDescent
