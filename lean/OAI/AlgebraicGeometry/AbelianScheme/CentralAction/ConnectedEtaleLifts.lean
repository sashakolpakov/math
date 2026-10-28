import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleEqualityIs
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Connected Etale Lifts -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ConnectedEtaleLifts.Construction

noncomputable section

/-! Two lifts through a finite etale morphism on a connected scheme
coincide once they agree at a single nonempty test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem finite_etale_sections_equal_of_connected
    {S : Scheme.{u}} [PreconnectedSpace S] {H : Over S}
    [IsFinite H.hom] [Etale H.hom]
    (a b : Over.mk (𝟙 S) ⟶ H) {T : Over S} [Nonempty T.left]
    (z : T ⟶ Over.mk (𝟙 S)) (hz : z ≫ a = z ≫ b) : a = b := by
  have : IsFinite (Over.mk (𝟙 S)).hom := inferInstanceAs (IsFinite (𝟙 S))
  have : Etale (Over.mk (𝟙 S)).hom := inferInstanceAs (Etale (𝟙 S))
  have : PreconnectedSpace (Over.mk (𝟙 S)).left := inferInstanceAs (PreconnectedSpace S)
  have hs := (TorsionQuotient.EtaleEqualityIs.EtaleEquality.equalizes_iff_range_subset a b z).mp hz
  have hnon : (Set.univ ∩ Set.range (equalizer.ι a b).left).Nonempty := by
    obtain ⟨t⟩ := ‹Nonempty T.left›
    exact ⟨z.left t, Set.mem_univ _, hs ⟨t, rfl⟩⟩
  have hall := isPreconnected_univ.subset_isClopen (TorsionQuotient.EtaleEqualityIs.EtaleEquality.range_isClopen a b) hnon
  have hid := (TorsionQuotient.EtaleEqualityIs.EtaleEquality.equalizes_iff_range_subset a b (𝟙 _)).mpr
    (fun _ _ => hall (Set.mem_univ _))
  simpa only [Category.id_comp] using hid

theorem finite_etale_lifts_equal_of_connected
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f] [PreconnectedSpace Z]
    (a b : Z ⟶ X) (hab : a ≫ f = b ≫ f)
    {T : Scheme.{u}} [Nonempty T] (z : T ⟶ Z) (hz : z ≫ a = z ≫ b) : a = b := by
  let H : Over Z := Over.mk (pullback.snd f (a ≫ f))
  let aa : Over.mk (𝟙 Z) ⟶ H := Over.homMk
    (pullback.lift a (𝟙 Z) (Category.id_comp _).symm) (pullback.lift_snd _ _ _)
  let bb : Over.mk (𝟙 Z) ⟶ H := Over.homMk
    (pullback.lift b (𝟙 Z) (hab.symm.trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)
  have : IsFinite H.hom := inferInstanceAs (IsFinite (pullback.snd f (a ≫ f)))
  have : Etale H.hom := inferInstanceAs (Etale (pullback.snd f (a ≫ f)))
  let zz : Over.mk z ⟶ Over.mk (𝟙 Z) := Over.homMk z (Category.comp_id _)
  have : Nonempty (Over.mk z).left := inferInstanceAs (Nonempty T)
  have hzz : zz ≫ aa = zz ≫ bb := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Over.comp_left, Over.homMk_left, aa, bb, zz, Category.assoc,
        pullback.lift_fst] using hz
    · simp only [Over.comp_left, Over.homMk_left, aa, bb, zz, Category.assoc, pullback.lift_snd]
  have he := finite_etale_sections_equal_of_connected aa bb zz hzz
  have he' := congrArg (fun j => j.left ≫ pullback.fst f (a ≫ f)) he
  simpa only [aa, bb, Over.homMk_left, pullback.lift_fst] using he'

theorem preconnected_of_geometricallyConnected_over_field
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [GeometricallyConnected f] : PreconnectedSpace X := by
  have h := (f.isConnected_preimage_singleton (default : Spec (.of k))).isPreconnected
  have he : f ⁻¹' ({default} : Set (Spec (.of k))) = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [he] at h
  exact ⟨h⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ConnectedEtaleLifts.Construction
