import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Complement
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedSmoothCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.SchemeImage

/-! # Disjoint Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.DisjointCenter.Construction

noncomputable section

/-! A center disjoint from the blown-up center pulls back isomorphically as an actual closed subscheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem isIso_pullback_snd_of_isIso_on_open
    {Y X Z : Scheme.{u}} (π : Y ⟶ X) (j : Z ⟶ X) (U : X.Opens)
    [IsIso (π ∣_ U)] (hj : Set.range j ⊆ U) : IsIso (pullback.snd π j) := by
  let k := IsOpenImmersion.lift U.ι j (by simpa only [Scheme.Opens.range_ι] using hj)
  have hk : k ≫ U.ι = j := IsOpenImmersion.lift_fac U.ι j _
  have h := (IsPullback.of_hasPullback (π ∣_ U) k).paste_horiz (isPullback_morphismRestrict π U).flip
  rw [hk] at h
  rw [← h.isoPullback_inv_snd]
  infer_instance

def closedPullbackToBase {Y X : Scheme.{u}} (π : Y ⟶ X) (L : X.IdealSheafData) :
    (L.comap π).subscheme ⟶ L.subscheme :=
  (L.comapIso π).hom ≫ pullback.snd π L.subschemeι

theorem closedPullbackToBase_over {Y X : Scheme.{u}} (π : Y ⟶ X) (L : X.IdealSheafData) :
    closedPullbackToBase π L ≫ L.subschemeι = (L.comap π).subschemeι ≫ π := by
  rw [closedPullbackToBase, Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

theorem globalBlowup_disjoint_center_isIso
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hdisjoint : K ⊔ L = ⊤) :
    IsIso (closedPullbackToBase (GlobalBlowup.Data.Construction.globalBlowupToBase K hK) L) := by
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase K hK
  let : IsIso (π ∣_ K.support.compl) := Complement.Construction.globalBlowup_supportComplement_isIso K hK
  have hj : Set.range L.subschemeι ⊆ K.support.compl := by
    rintro x ⟨z, rfl⟩ hx
    have hs := congrArg Scheme.IdealSheafData.support hdisjoint
    rw [Scheme.IdealSheafData.support_sup, Scheme.IdealSheafData.support_top] at hs
    have hm : L.subschemeι z ∈ K.support ⊓ L.support := ⟨hx, z.property⟩
    rw [hs] at hm
    exact hm
  let : IsIso (pullback.snd π L.subschemeι) := isIso_pullback_snd_of_isIso_on_open π L.subschemeι _ hj
  unfold closedPullbackToBase
  infer_instance

theorem globalBlowup_disjoint_center_smooth
    {X B : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ B) (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hdisjoint : K ⊔ L = ⊤)
    [Smooth (L.subschemeι ≫ f)] :
    Smooth ((L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK)).subschemeι ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ f)) := by
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase K hK
  let : IsIso (closedPullbackToBase π L) := globalBlowup_disjoint_center_isIso K L hK hdisjoint
  have he : closedPullbackToBase π L ≫ (L.subschemeι ≫ f) =
      (L.comap π).subschemeι ≫ (π ≫ f) := by
    rw [← Category.assoc, closedPullbackToBase_over, Category.assoc]
  exact he ▸ (inferInstance : Smooth (closedPullbackToBase π L ≫ (L.subschemeι ≫ f)))

theorem globalBlowup_disjoint_center_integral
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hdisjoint : K ⊔ L = ⊤) [IsIntegral L.subscheme] :
    IsIntegral (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK)).subscheme := by
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase K hK
  let j := closedPullbackToBase π L
  let : IsIso j := globalBlowup_disjoint_center_isIso K L hK hdisjoint
  let : Nonempty (L.comap π).subscheme := ⟨inv j (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion j

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.DisjointCenter.Construction
