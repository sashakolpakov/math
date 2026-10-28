import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.BaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Interface
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition

/-! # Generic Moduli -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GenericModuli.Construction

noncomputable section

/-! The reduced fine-moduli property passes to the actual generic fiber.
Canonical PEL pullback comparisons retain every piece of family data. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

def modelClassifyingMap (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    {T : Over (Spec (.of K))} (x : T ⟶ D.space) :
    (Over.map D.generic).obj T ⟶ D.model.space :=
  ((Over.mapPullbackAdj D.generic).homEquiv T D.model.space).symm x

theorem modelClassifyingMap_left (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    {T : Over (Spec (.of K))} (x : T ⟶ D.space) :
    (modelClassifyingMap D x).left = x.left ≫ pullback.fst D.model.space.hom D.generic := rfl

/-- A full PEL isomorphism forces equality of generic-fiber classifying
maps on every reduced test scheme, with no restriction to one component. -/
theorem generic_classifying_maps_eq_of_pelIso
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    {T : Over (Spec (.of K))} [IsReduced T.left] (x y : T ⟶ D.space)
    (e : TateComparison.PELModuli.PELFamilyIso (D.family.pullback x.left) (D.family.pullback y.left)) : x = y := by
  have : IsReduced ((Over.map D.generic).obj T).left := inferInstanceAs (IsReduced T.left)
  apply ((Over.mapPullbackAdj D.generic).homEquiv T D.model.space).symm.injective
  let ex := BaseChange.Construction.pelPullbackComp D.model.family (pullback.fst D.model.space.hom D.generic) x.left
  let ey := BaseChange.Construction.pelPullbackComp D.model.family (pullback.fst D.model.space.hom D.generic) y.left
  exact BaseChange.Construction.classifying_maps_eq_of_pelIso D.model D.baseAction hgeometry.classifies
    ((Over.map D.generic).obj T) (modelClassifyingMap D x) (modelClassifyingMap D y)
    (ex.symm.trans (e.trans ey))

/-- The generic universal family has the actual Rosati condition supplied
by the fine PEL moduli problem. It is not extra scalar-action data. -/
theorem generic_family_rosati
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry) :
    D.family.IsRosatiCompatible (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom := by
  have : Smooth D.model.space.hom := hgeometry.smooth
  have : Smooth D.space.hom := inferInstanceAs
    (Smooth (pullback.snd D.model.space.hom D.generic))
  have : IsReduced D.space.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced D.space.hom
  let T : Over (TateComparison.Data.modelBase K D.denominator) :=
    Over.mk (pullback.fst D.model.space.hom D.generic ≫ D.model.space.hom)
  let x : T ⟶ D.model.space := Over.homMk (pullback.fst D.model.space.hom D.generic) rfl
  have : IsReduced T.left := inferInstanceAs (IsReduced D.space.left)
  exact (hgeometry.classifies.1 T x).1.2.2

/-- The polarization type on the generic universal family is the same
fixed type on every component and every geometric fiber. -/
theorem generic_family_polarizationType
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry) :
    D.family.polarizationMap.HasPolarizationType D.reference.polarizationType := by
  have : Smooth D.model.space.hom := hgeometry.smooth
  have : Smooth D.space.hom := inferInstanceAs
    (Smooth (pullback.snd D.model.space.hom D.generic))
  have : IsReduced D.space.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced D.space.hom
  let T : Over (TateComparison.Data.modelBase K D.denominator) :=
    Over.mk (pullback.fst D.model.space.hom D.generic ≫ D.model.space.hom)
  let x : T ⟶ D.model.space := Over.homMk (pullback.fst D.model.space.hom D.generic) rfl
  have : IsReduced T.left := inferInstanceAs (IsReduced D.space.left)
  exact (hgeometry.classifies.1 T x).1.1

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GenericModuli.Construction
