import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Mono Open Section -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.MonoOpenSection

noncomputable section

/-! A local section of a scheme monomorphism identifies the whole
inverse image of its open domain. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

theorem monoOpenSection_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f]
    (U : Y.Opens) (j : U.toScheme ⟶ X) (hj : j ≫ f = U.ι) : IsOpenImmersion j := by
  let g : U.toScheme ⟶ pullback f U.ι := pullback.lift j (𝟙 _) (by simpa using hj)
  let e : U.toScheme ≅ pullback f U.ι :=
    { hom := g
      inv := pullback.snd f U.ι
      hom_inv_id := pullback.lift_snd _ _ _
      inv_hom_id := by
        apply (cancel_mono (pullback.snd f U.ι)).mp
        simp only [Category.assoc, g, pullback.lift_snd, Category.comp_id, Category.id_comp] }
  have he : j = e.hom ≫ pullback.fst f U.ι := (pullback.lift_fst _ _ _).symm
  have : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  have : IsOpenImmersion (pullback.fst f U.ι) := inferInstance
  have h : IsOpenImmersion (e.hom ≫ pullback.fst f U.ι) := inferInstance
  exact he ▸ h

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.MonoOpenSection
