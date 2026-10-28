import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Isomorphisms

/-! # Ample Affine Factor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A relatively ample line bundle becomes ample after an affine test scheme whose map factors through one affine open of the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.IsRelativelyAmple.isAmple_after_affine_open_factor
    {S X T P : Scheme.{u}} [IsAffine T] {f : X ⟶ S}
    {L : Line.Bundles.LineBundle X} (hL : L.IsRelativelyAmple f)
    (U : S.Opens) (hU : IsAffineOpen U) (c : T ⟶ U.toScheme)
    {a : P ⟶ X} {b : P ⟶ T} (H : IsPullback a b f (c ≫ U.ι)) :
    (L.pullback a).IsAmple := by
  let W := f ⁻¹ᵁ U
  let B := (isPullback_morphismRestrict f U).flip
  have hw : a ≫ f = (b ≫ c) ≫ U.ι := H.w.trans (Category.assoc b c U.ι).symm
  let v : P ⟶ W.toScheme := B.lift a (b ≫ c) hw
  have hv : v ≫ W.ι = a := B.lift_fst _ _ _
  have hq : v ≫ (f ∣_ U) = b ≫ c := B.lift_snd _ _ _
  have Houter : IsPullback b (v ≫ W.ι) (c ≫ U.ι) f :=
    (congrArg (fun z => IsPullback b z (c ≫ U.ι) f) hv).mpr H.flip
  have Hv : IsPullback b v c (f ∣_ U) := Houter.of_bot hq.symm B.flip
  have : IsAffine U.toScheme := hU
  have : IsAffineHom v := MorphismProperty.of_isPullback Hv (inferInstance : IsAffineHom c)
  exact ((hL U hU).pullback_of_isAffineHom v).of_iso
    ((Scheme.Modules.pullbackComp v W.ι).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr hv).app L.sheaf)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
