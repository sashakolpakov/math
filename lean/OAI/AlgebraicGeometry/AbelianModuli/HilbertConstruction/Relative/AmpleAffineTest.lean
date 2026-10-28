import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.AmpleAffineFactor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffineOpenCover

/-! # Ample Affine Test -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A relatively ample bundle on a proper scheme becomes ample after every affine scheme test of the base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.IsRelativelyAmple.isAmple_after_affine_cartesian
    {S X T P : Scheme.{u}} [IsAffine T] {f : X ⟶ S} [IsProper f]
    {L : Line.Bundles.LineBundle X} (hL : L.IsRelativelyAmple f)
    {a : P ⟶ X} {b : P ⟶ T} {g : T ⟶ S} (H : IsPullback a b f g) :
    (L.pullback a).IsAmple := by
  have hnb (t : T) : ∃ (U : S.Opens) (V : T.Opens),
      t ∈ V ∧ IsAffineOpen U ∧ IsAffineOpen V ∧ V ≤ g ⁻¹ᵁ U := by
    obtain ⟨_, ⟨U : S.Opens, hU, rfl⟩, htU, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g t)) isOpen_univ
    obtain ⟨_, ⟨V : T.Opens, hV, rfl⟩, htV, hVU⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (show t ∈ g ⁻¹ᵁ U from htU) (g ⁻¹ᵁ U).isOpen
    exact ⟨U, V, htV, hU, hV, hVU⟩
  choose U V ht hU hV hVU using hnb
  have hcover : iSup V = ⊤ := by
    apply top_unique
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, ht t⟩
  let C := T.openCoverOfIsOpenCover V hcover
  have (i : C.I₀) : IsAffine (C.X i) := hV i
  have : IsProper b := MorphismProperty.of_isPullback H (inferInstance : IsProper f)
  apply (L.pullback a).isAmple_of_affine_open_cover b C
  intro i
  let d := pullback.fst b (V i).ι
  let q := pullback.snd b (V i).ι
  let c := g.resLE (U i) (V i) (hVU i)
  have H₀ : IsPullback (d ≫ a) q f ((V i).ι ≫ g) :=
    ((IsPullback.of_hasPullback b (V i).ι).flip.paste_vert H.flip).flip
  have H' : IsPullback (d ≫ a) q f (c ≫ (U i).ι) :=
    (congrArg (fun r => IsPullback (d ≫ a) q f r) (g.resLE_comp_ι (hVU i))).mpr H₀
  have : IsAffine (V i).toScheme := hV i
  exact (hL.isAmple_after_affine_open_factor (U i) (hU i) c H').of_iso
    ((Scheme.Modules.pullbackComp d a).app L.sheaf).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
