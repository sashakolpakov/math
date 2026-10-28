import Mathlib

/-! # Forget Sheafification -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ForgetSheafification

noncomputable section

section

/-! Forgetting complex scalars preserves sheafification by the unchanged local section conditions. -/

open _root_.CategoryTheory _root_.TopologicalSpace

theorem complexAdditivePreservesSheafification (X : TopCat.{0}) :
    (Opens.grothendieckTopology X).PreservesSheafification
      (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) where
  le P Q a ha := by
    let J := Opens.grothendieckTopology X
    change J.W (Functor.whiskerRight a (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}))
    have hi : Presheaf.IsLocallyInjective J a := ha.isLocallyInjective
    have hs : Presheaf.IsLocallySurjective J a := ha.isLocallySurjective
    apply (J.W_iff_isLocallyBijective _).mpr
    constructor
    · exact { equalizerSieve_mem := fun x y h => Presheaf.equalizerSieve_mem J a x y h }
    · exact { imageSieve_mem := fun s => Presheaf.imageSieve_mem J a s }

def complexAdditiveSheafificationIso (X : TopCat.{0}) :
    (Functor.whiskeringRight (Opens X)ᵒᵖ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).obj
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) ⋙
        presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} ≅
      presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ) ⋙
        sheafCompose (Opens.grothendieckTopology X)
          (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) := by
  have := complexAdditivePreservesSheafification X
  exact sheafComposeNatIso (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})
    (sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ))
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{0})

end

/-! The coefficient-forgetting isomorphism preserves the actual
sheafification unit, not merely the isomorphism class of the sheaf. -/

open _root_.CategoryTheory _root_.TopologicalSpace

theorem complexAdditiveSheafificationIso_unit (X : TopCat.{0})
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) :
    toSheafify (Opens.grothendieckTopology X)
        (P ⋙ forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) ≫
      ((complexAdditiveSheafificationIso X).app P).hom.hom =
        Functor.whiskerRight (toSheafify (Opens.grothendieckTopology X) P)
          (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) :=
  sheafComposeNatTrans_fac (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})
    (sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ))
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{0}) P

end

end OAI.AlgebraicGeometry.Comparison.Betti.ForgetSheafification
