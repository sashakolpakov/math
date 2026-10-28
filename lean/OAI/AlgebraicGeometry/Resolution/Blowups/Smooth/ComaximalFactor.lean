import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterComponents
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhood

/-! # Comaximal Factor -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ComaximalFactor.Construction

noncomputable section

/-! A comaximal factor of a smooth center is an actual open-and-closed smooth subcenter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem closedImmersion_isOpenImmersion_of_open_range
    {Y X : Scheme} [IsReduced X] (j : Y ⟶ X) [IsClosedImmersion j]
    (hopen : IsOpen (Set.range j)) : IsOpenImmersion j := by
  let U : X.Opens := ⟨Set.range j, hopen⟩
  let k := IsOpenImmersion.lift U.ι j (by rw [Scheme.Opens.range_ι]; exact Set.Subset.refl _)
  have hk : k ≫ U.ι = j := IsOpenImmersion.lift_fac U.ι j _
  let : IsClosedImmersion (k ≫ U.ι) := hk.symm ▸ inferInstance
  let : IsClosedImmersion k := IsClosedImmersion.of_comp k U.ι
  let : IsReduced U := isReduced_of_isOpenImmersion U.ι
  let : Surjective k := by
    constructor
    intro x
    obtain ⟨y, hy⟩ := x.property
    refine ⟨y, U.ι.injective ?_⟩
    change (k ≫ U.ι) y = x.val
    rw [hk]
    exact hy
  let : IsIso k := isIso_of_isClosedImmersion_of_surjective k
  rw [← hk]
  infer_instance

theorem comaximal_factor_subscheme_isOpenImmersion
    {X : Scheme} (K L : X.IdealSheafData) (hdisjoint : K ⊔ L = ⊤)
    [IsReduced (K * L).subscheme] :
    IsOpenImmersion (Scheme.IdealSheafData.inclusion (show K * L ≤ L from fun _ => Ideal.mul_le_right)) := by
  let I := K * L
  let i := Scheme.IdealSheafData.inclusion (show I ≤ L from fun _ => Ideal.mul_le_right)
  have hi : i ≫ I.subschemeι = L.subschemeι := Scheme.IdealSheafData.inclusion_subschemeι _
  let : IsClosedImmersion (i ≫ I.subschemeι) := hi.symm ▸ inferInstance
  let : IsClosedImmersion i := IsClosedImmersion.of_comp i I.subschemeι
  have hr : Set.range i = (I.subschemeι ⁻¹ᵁ K.support.compl : I.subscheme.Opens) := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      have hw : I.subschemeι (i w) ∈ L.support := by
        change (i ≫ I.subschemeι) w ∈ L.support
        rw [hi]
        exact w.property
      exact Global.ResidualNeighborhood.Construction.idealSheaf_support_subset_complement_of_sup_top L K (by rwa [sup_comm]) hw
    · intro hz
      have hzI := z.property
      change z.val ∈ K.support ⊔ L.support at hzI
      have hzL : z.val ∈ L.support := hzI.resolve_left hz
      refine ⟨⟨z.val, hzL⟩, I.subschemeι.injective ?_⟩
      change (i ≫ I.subschemeι) ⟨z.val, hzL⟩ = z.val
      rw [hi]
      rfl
  exact closedImmersion_isOpenImmersion_of_open_range i (hr ▸ (I.subschemeι ⁻¹ᵁ K.support.compl).isOpen)

theorem smooth_comaximal_right_factor
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K L : X.IdealSheafData) (hdisjoint : K ⊔ L = ⊤)
    [Smooth ((K * L).subschemeι ≫ f)] : Smooth (L.subschemeι ≫ f) := by
  let I := K * L
  let : IsReduced I.subscheme := CenterComponents.Construction.smooth_complex_scheme_isReduced (I.subschemeι ≫ f)
  let i := Scheme.IdealSheafData.inclusion (show I ≤ L from fun _ => Ideal.mul_le_right)
  let : IsOpenImmersion i := comaximal_factor_subscheme_isOpenImmersion K L hdisjoint
  have hi : i ≫ I.subschemeι = L.subschemeι := Scheme.IdealSheafData.inclusion_subschemeι _
  have hs : Smooth (i ≫ (I.subschemeι ≫ f)) := inferInstance
  rw [← Category.assoc, hi] at hs
  exact hs

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ComaximalFactor.Construction
