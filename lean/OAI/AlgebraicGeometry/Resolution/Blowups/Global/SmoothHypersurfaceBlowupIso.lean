import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HypersurfaceNormalCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.FramedHypersurfaceKernel
import OAI.AlgebraicGeometry.Resolution.Blowups.CenterClosedBlowupKernel
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedTransformMap

/-! # Smooth Hypersurface Blowup Iso -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothHypersurfaceBlowupIso.Construction

noncomputable section

section

/-! The actual controlled transform of a smooth integral Cartier hypersurface is its intrinsic blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

local instance (H : X.IdealSheafData) : IsLocallyNoetherian H.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian H.subschemeι

theorem globalBlowupMap_kernel_controlled_on_unit_center
    (I H : X.IdealSheafData) (hI : I ≠ ⊥) [IsIntegral H.subscheme]
    (hH : I.comap H.subschemeι ≠ ⊥) (U : X.affineOpens) (hunit : I.ideal U = ⊤) :
    (GlobalBlowup.FunctorialMap.Construction.globalBlowupMap H.subschemeι I hI hH).ker.comap (GlobalBlowup.Data.Construction.globalBlowupChart I hI U) =
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).comap (GlobalBlowup.Data.Construction.globalBlowupChart I hI U) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  let q := H.subschemeι
  let V : H.subscheme.affineOpens := ⟨q ⁻¹ᵁ U.1, U.2.preimage q⟩
  let φ := (q.appLE U.1 V.1 le_rfl).hom
  have hφ : Function.Surjective φ := by
    change Function.Surjective (H.subschemeι.appLE U.1 (H.subschemeι ⁻¹ᵁ U.1) le_rfl).hom
    rw [Scheme.Hom.appLE_eq_app]
    exact H.subschemeι_app_surjective U
  have hk : RingHom.ker φ = H.ideal U := by
    change RingHom.ker (H.subschemeι.appLE U.1 (H.subschemeι ⁻¹ᵁ U.1) le_rfl).hom = _
    rw [Scheme.Hom.appLE_eq_app, H.ker_subschemeι_app]
  let : IsClosedImmersion (GlobalBlowup.FunctorialMap.Construction.globalBlowupMap q I hI hH) :=
    GlobalBlowup.ClosedImmersion.Construction.globalBlowupMap_isClosedImmersion q I hI hH
  rw [ClosedCarrierCenters.Construction.kernel_comap_of_closed_pullback _ _ _ _ (GlobalBlowup.ClosedImmersion.Construction.globalBlowupMap_affine_isPullback q I hI hH U),
    Affine.BlowupClosedKernel.Construction.affineBlowupMapTo_ker_eq_map, GlobalControlled.BaseChangeCharts.Construction.globalBlowupControlledIdeal_comap_affineBlowup]
  exact CenterClosedBlowupKernel.Construction.affineBlowupMap_unitCenter_ker (I.ideal U) (H.ideal U) hunit φ hφ hk 1

/-- No exceptional component is added to a smooth Cartier carrier: its
controlled ideal is exactly the kernel of the intrinsic blowup comparison. -/
theorem globalBlowupMap_kernel_eq_smooth_hypersurface_controlled
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [IsIntegral H.subscheme] [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I) (hIH : I.comap H.subschemeι ≠ ⊥) :
    (GlobalBlowup.FunctorialMap.Construction.globalBlowupMap H.subschemeι I hI hIH).ker = GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1 := by
  classical
  choose U hxU hcase using HypersurfaceNormalCover.Construction.exists_global_hypersurface_normal_neighborhood f I H hH hlocal hHI
  have hcover : ⨆ x : X, (U x).1 = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
  let : IsClosedImmersion (GlobalBlowup.FunctorialMap.Construction.globalBlowupMap H.subschemeι I hI hIH) :=
    GlobalBlowup.ClosedImmersion.Construction.globalBlowupMap_isClosedImmersion H.subschemeι I hI hIH
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (GlobalBlowup.MapGluing.Construction.globalBlowupChosenCover I hI U hcover)
  intro x
  change X at x
  change (GlobalBlowup.FunctorialMap.Construction.globalBlowupMap H.subschemeι I hI hIH).ker.comap (GlobalBlowup.Data.Construction.globalBlowupChart I hI (U x)) =
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).comap (GlobalBlowup.Data.Construction.globalBlowupChart I hI (U x))
  rcases hcase x with ht | hn
  · exact globalBlowupMap_kernel_controlled_on_unit_center I H hI hIH (U x) ht
  · let : Algebra ℂ Γ(X, U x) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (U x)
    obtain ⟨ι, hdec, g, D, hD, hgen, j, hnormal⟩ := hn
    exact FramedHypersurfaceKernel.Construction.globalBlowupMap_kernel_controlled_on_normal_frame f I H hI hIH (U x) g D hD hgen j hnormal

theorem globalBlowup_smooth_hypersurface_controlled_eq_strict
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [IsIntegral H.subscheme] [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I) (hIH : I.comap H.subschemeι ≠ ⊥) :
    letI : IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ I.support.compl) :=
      Blowup.Complement.Construction.globalBlowup_supportComplement_isIso I hI
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1 =
      Integral.StrictTransform.Construction.strictTransformIdeal (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) H I.support.compl :=
  (globalBlowupMap_kernel_eq_smooth_hypersurface_controlled f I H hI hH hlocal hHI hIH).symm.trans
    (GlobalBlowup.StrictComparison.Construction.globalBlowupMap_kernel_eq_strictTransform I H hI hIH)

theorem globalBlowup_smooth_hypersurface_controlled_isIntegral
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [IsIntegral H.subscheme] [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I) (hIH : I.comap H.subschemeι ≠ ⊥) :
    IsIntegral (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme := by
  rw [← globalBlowupMap_kernel_eq_smooth_hypersurface_controlled f I H hI hH hlocal hHI hIH]
  let : IsClosedImmersion (GlobalBlowup.FunctorialMap.Construction.globalBlowupMap H.subschemeι I hI hIH) :=
    GlobalBlowup.ClosedImmersion.Construction.globalBlowupMap_isClosedImmersion H.subschemeι I hI hIH
  exact Integral.SchemeImage.Construction.scheme_image_isIntegral (GlobalBlowup.FunctorialMap.Construction.globalBlowupMap H.subschemeι I hI hIH)

end

/-! The smooth controlled hypersurface is isomorphic over its original carrier to its own actual blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

local instance (H : X.IdealSheafData) : IsLocallyNoetherian H.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian H.subschemeι

theorem globalBlowup_smooth_hypersurface_iso
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [IsIntegral H.subscheme] [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I) (hIH : I.comap H.subschemeι ≠ ⊥) :
    ∃ e : GlobalBlowup.Data.Construction.globalBlowup (I.comap H.subschemeι) hIH ≅ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme,
      e.hom ≫ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι = GlobalBlowup.FunctorialMap.Construction.globalBlowupMap H.subschemeι I hI hIH ∧
      e.hom ≫ ClosedTransformMap.Construction.closedTransformMap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) H (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1)
        (GlobalControlled.Ideal.Construction.totalIdeal_le_controlledIdealSheaf I H 1 (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) =
          GlobalBlowup.Data.Construction.globalBlowupToBase (I.comap H.subschemeι) hIH := by
  let L := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
  let ρ := GlobalBlowup.FunctorialMap.Construction.globalBlowupMap H.subschemeι I hI hIH
  let : IsClosedImmersion ρ := GlobalBlowup.ClosedImmersion.Construction.globalBlowupMap_isClosedImmersion H.subschemeι I hI hIH
  have hk : ρ.ker = L.subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact globalBlowupMap_kernel_eq_smooth_hypersurface_controlled f I H hI hH hlocal hHI hIH
  let l := IsClosedImmersion.lift L.subschemeι ρ hk.symm.le
  have hl : l ≫ L.subschemeι = ρ := IsClosedImmersion.lift_fac _ _ _
  let : IsIso l := IsClosedImmersion.isIso_of_ker_eq ρ L.subschemeι l hl hk
  refine ⟨asIso l, hl, ?_⟩
  apply (cancel_mono H.subschemeι).mp
  have htotal : H.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≤ L :=
    GlobalControlled.Ideal.Construction.totalIdeal_le_controlledIdealSheaf I H 1 (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
  change (l ≫ ClosedTransformMap.Construction.closedTransformMap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) H L htotal) ≫ H.subschemeι = _
  rw [Category.assoc, ClosedTransformMap.Construction.closedTransformMap_over (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) H L htotal,
    ← Category.assoc]
  rw [hl]
  exact GlobalBlowup.FunctorialMap.Construction.globalBlowupMap_over H.subschemeι I hI hIH

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothHypersurfaceBlowupIso.Construction
