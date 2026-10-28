import Mathlib.CategoryTheory.Sites.Equivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AdditiveSheafRestriction

/-! # Scheme Isomorphism Additive Sheaves -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeIsomorphismAdditiveSheaves.ZariskiCohomology

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

noncomputable def sheafEquivOfSchemeIso
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf X ≌ Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.AbSheaf Y := by
  let eb : (X : TopCat) ≅ (Y : TopCat) := asIso e.hom.base
  let eo := Opens.mapMapIso eb
  letI : eo.functor.IsCocontinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
    (eo.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
      (coverPreserving_opens_map eb.inv)
  letI : eo.inverse.IsCocontinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) :=
    (eo.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
      (coverPreserving_opens_map eb.hom)
  letI : eo.functor.IsDenseSubsite
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
    eo.isDenseSubsite_functor_of_isCocontinuous _ _
  exact (Functor.IsDenseSubsite.sheafEquiv
    (G := eo.functor)
    (K := Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y)
    AddCommGrpCat.{u}).symm

noncomputable def pushforwardConstantIso
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base).obj
        ((CategoryTheory.constantSheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift ℤ))) ≅
      (CategoryTheory.constantSheaf
        (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ)) := by
  let eb : (X : TopCat) ≅ (Y : TopCat) := asIso e.hom.base
  let eo := Opens.mapMapIso eb
  letI : eo.functor.IsCocontinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
    (eo.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
      (coverPreserving_opens_map eb.inv)
  letI : eo.inverse.IsCocontinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) :=
    (eo.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
      (coverPreserving_opens_map eb.hom)
  letI : eo.functor.IsDenseSubsite
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
    eo.isDenseSubsite_functor_of_isCocontinuous _ _
  exact (equivCommuteConstant'
    (Opens.grothendieckTopology Y)
    AddCommGrpCat.{u}
    (Opens.grothendieckTopology X)
    eo.functor
    (isTerminalTop : IsTerminal (⊤ : Opens Y))
    (isTerminalTop : IsTerminal (⊤ : Opens X))).symm.app
      (AddCommGrpCat.of (ULift ℤ))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeIsomorphismAdditiveSheaves.ZariskiCohomology
