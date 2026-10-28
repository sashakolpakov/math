import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Topology.Sheaves.Abelian

/-! # Scalar Forgetting Sheafification -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ScalarForgettingSheafification

noncomputable section

section

/-! # Forgetting scalars preserves local sheafification equivalences

The underlying sections, equalizer sieves and local-preimage sieves are
unchanged. Thus literal scalar forgetting preserves local bijections, which
are exactly the morphisms inverted by sheafification.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (R : Type) [CommRing R] (Y : TopCat.{0})

/-- The same local sections prove the scalar-forgotten sheafification equivalence. -/
instance scalarForgetting_preservesSheafification :
    (Opens.grothendieckTopology Y).PreservesSheafification
      (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) where
  le _ _ f hf := by
    obtain ⟨hi, hs⟩ :=
      ((Opens.grothendieckTopology Y).W_iff_isLocallyBijective f).mp hf
    have hi' : Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
        (Functor.whiskerRight f (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})) :=
      ⟨fun {U} x y h => hi.equalizerSieve_mem x y h⟩
    have hs' : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
        (Functor.whiskerRight f (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})) :=
      ⟨fun {U} x => hs.imageSieve_mem x⟩
    exact ((Opens.grothendieckTopology Y).W_iff_isLocallyBijective _).mpr ⟨hi', hs'⟩

end

/-! # The canonical comparison of actual scalar sheafification functors

All coefficient objects and morphisms are in the same small universe as the
original singular complexes. Preservation follows from the proved equality
of the actual local-section sieves.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (R : Type) [CommRing R] (Y : TopCat.{0})

local notation "J" => Opens.grothendieckTopology Y

set_option backward.isDefEq.respectTransparency false in
/-- The canonical scalar-forgetting comparison on all actual presheaves. -/
def scalarSheafificationCanonicalIso :
    (Functor.whiskeringRight (Opens Y)ᵒᵖ (ModuleCat.{0} R) AddCommGrpCat.{0}).obj
        (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) ⋙
        presheafToSheaf J AddCommGrpCat.{0} ≅
      presheafToSheaf J (ModuleCat.{0} R) ⋙
        sheafCompose J (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) :=
  sheafComposeNatIso J (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})
    (sheafificationAdjunction J (ModuleCat.{0} R))
    (sheafificationAdjunction J AddCommGrpCat.{0})

set_option backward.isDefEq.respectTransparency false in
/-- The actual units commute with the canonical scalar-forgetting comparison. -/
theorem scalarSheafificationCanonicalIso_unit (P : (Opens Y)ᵒᵖ ⥤ ModuleCat.{0} R) :
    toSheafify J (P ⋙ forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) ≫
        ((scalarSheafificationCanonicalIso R Y).app P).hom.hom =
      Functor.whiskerRight (toSheafify J P) (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) :=
  sheafComposeNatTrans_fac J (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})
    (sheafificationAdjunction J (ModuleCat.{0} R))
    (sheafificationAdjunction J AddCommGrpCat.{0}) P

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ScalarForgettingSheafification
