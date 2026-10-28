import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Scheme Image Dominance -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeImageDominance.Construction

noncomputable section

/-! A quasi-compact morphism is scheme-theoretically dominant onto its
actual scheme-theoretic image, including nonreduced images. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite

universe u

theorem toImage_app_injective {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : f.image.Opens) : Function.Injective (f.toImage.app U) :=
  TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
    (F := ⟨f.image.presheaf, f.image.IsSheaf⟩) f.toImage.c U
      (fun x _ => f.stalkFunctor_toImage_injective x)

theorem toImage_schemeTheoreticallyDominant {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  constructor
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.Hom.ker_apply]
  change RingHom.ker (f.toImage.app U.1).hom = ⊥
  exact (RingHom.injective_iff_ker_eq_bot (f.toImage.app U.1).hom).mp (toImage_app_injective f U.1)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeImageDominance.Construction
