import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Ideal Sheaf Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Open.IdealSheafBaseChange.Construction

noncomputable section

/-! Exact pullback of quasi-compact kernel ideals along open immersions,
and the corresponding base-change law for ideal sheaf extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- A quasi-compact morphism's kernel ideal sheaf restricts exactly
along an actual open pullback square. -/
theorem kernel_comap_of_open_pullback
    {S X T Y : Scheme.{u}} (g : S ⟶ Y) (g' : T ⟶ X) (i : T ⟶ S) (f : X ⟶ Y)
    [IsOpenImmersion f] [QuasiCompact g] (hpb : IsPullback g' i f g) :
    g.ker.comap f = g'.ker := by
  ext1
  funext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion g g' i f hpb W).symm

/-- Restriction of the extended ideal equals extension of its
restriction to the overlap. This is the actual ideal-sheaf base-change
identity needed for gluing along open subschemes. -/
theorem idealSheaf_open_comap_map
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [QuasiCompact g]
    (J : Y.IdealSheafData) :
    (J.map g).comap f =
      (J.comap (pullback.snd f g)).map (pullback.fst f g) := by
  let a := pullback.fst (pullback.snd f g) J.subschemeι
  let c := pullback.snd (pullback.snd f g) J.subschemeι
  have h1 := IsPullback.of_hasPullback (pullback.snd f g) J.subschemeι
  have h2 := IsPullback.of_hasPullback f g
  have houter : IsPullback (a ≫ pullback.fst f g) c f (J.subschemeι ≫ g) :=
    (h1.flip.paste_vert h2.flip).flip
  have he := kernel_comap_of_open_pullback (J.subschemeι ≫ g)
    (a ≫ pullback.fst f g) c f houter
  change (J.map g).comap f = (a.ker).map (pullback.fst f g)
  simpa only [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι] using he

/-- Open restriction commutes with finite intersections of ideal sheaves. -/
theorem idealSheaf_open_comap_iInf
    {X Y : Scheme.{u}} {ι : Type*} [Finite ι]
    (f : X ⟶ Y) [IsOpenImmersion f] (J : ι → Y.IdealSheafData) :
    (⨅ i, J i).comap f = ⨅ i, (J i).comap f := by
  ext1
  funext W
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_iInf, iInf_apply, Ideal.comap_iInf]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Open.IdealSheafBaseChange.Construction
