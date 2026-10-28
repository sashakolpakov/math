import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Transform
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.HypersurfaceCoefficient
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Nonzero

/-! # Upper -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Upper.Construction

noncomputable section

section

/-! The native retained coefficient upper bound persists through the actual carrier transform. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalRetainedCoefficientTransform_mono
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I H : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ)
    {C D : H.subscheme.IdealSheafData} (h : C ≤ D) :
    Transform.Construction.globalRetainedCoefficientTransform I H C hI b ≤ Transform.Construction.globalRetainedCoefficientTransform I H D hI b := by
  intro U
  exact Submodule.colon_mono ((Scheme.IdealSheafData.comap_mono (Transform.Construction.globalControlledCarrierMap I H hI) h) U) le_rfl

theorem globalRetainedCoefficientTransform_le_intrinsic
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I J H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [IsIntegral H.subscheme] [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I) (hIH : I.comap H.subschemeι ≠ ⊥)
    (b : ℕ) (hp : J ≤ I ^ b) (C : H.subscheme.IdealSheafData)
    (hupp : C ≤ CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι) :
    letI : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
    Transform.Construction.globalRetainedCoefficientTransform I H C hI b ≤
      CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) b (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι := by
  let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
  exact (globalRetainedCoefficientTransform_mono I H hI b hupp).trans
    (GlobalControlled.HypersurfaceCoefficient.Construction.globalHypersurfaceCoefficientTransform_le f I J H hI hH hlocal hHI hIH b hp)

end

section

/-! Retained native coefficients agree with their carrier blowup transform and remain nonzero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem retained_coefficient_center_ne_bot
    {X : Scheme} (I H : X.IdealSheafData) (C : H.subscheme.IdealSheafData) (b : ℕ)
    (hC : C ≠ ⊥) (hp : C ≤ (I.comap H.subschemeι) ^ b.factorial) : I.comap H.subschemeι ≠ ⊥ := by
  intro hz
  rw [hz, ← Scheme.IdealSheafData.zero_eq_bot, zero_pow (Nat.factorial_pos b).ne'] at hp
  exact hC (le_bot_iff.mp hp)

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

local instance retainedOriginalCarrierNoetherian (H : X.IdealSheafData) : IsLocallyNoetherian H.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian H.subschemeι

theorem exists_globalRetainedCoefficientTransform_carrier_iso
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [IsIntegral H.subscheme] [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I) (hIH : I.comap H.subschemeι ≠ ⊥)
    (C : H.subscheme.IdealSheafData) (b : ℕ) :
    ∃ e : GlobalBlowup.Data.Construction.globalBlowup (I.comap H.subschemeι) hIH ≅ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme,
      e.hom ≫ Transform.Construction.globalControlledCarrierMap I H hI = GlobalBlowup.Data.Construction.globalBlowupToBase (I.comap H.subschemeι) hIH ∧
      (Transform.Construction.globalRetainedCoefficientTransform I H C hI b).comap e.hom =
        GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (I.comap H.subschemeι) C hIH b.factorial := by
  obtain ⟨e, _, he⟩ := Global.SmoothHypersurfaceBlowupIso.Construction.globalBlowup_smooth_hypersurface_iso f I H hI hH hlocal hHI hIH
  have hover : e.hom ≫ Transform.Construction.globalControlledCarrierMap I H hI = GlobalBlowup.Data.Construction.globalBlowupToBase (I.comap H.subschemeι) hIH := he
  refine ⟨e, hover, ?_⟩
  rw [Transform.Construction.globalRetainedCoefficientTransform, GlobalControlled.Ideal.Construction.controlledIdealSheaf_comap_open, hover]
  rfl

theorem globalRetainedCoefficientTransform_ne_bot
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [IsIntegral H.subscheme] [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I)
    (C : H.subscheme.IdealSheafData) (b : ℕ) (hC : C ≠ ⊥)
    (hp : C ≤ (I.comap H.subschemeι) ^ b.factorial) :
    Transform.Construction.globalRetainedCoefficientTransform I H C hI b ≠ ⊥ := by
  have hIH := retained_coefficient_center_ne_bot I H C b hC hp
  obtain ⟨e, _, he⟩ := exists_globalRetainedCoefficientTransform_carrier_iso f I H hI hH hlocal hHI hIH C b
  intro hz
  rw [hz, Scheme.IdealSheafData.comap_bot] at he
  exact GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot (I.comap H.subschemeι) C hIH b.factorial hC he.symm

end

/-! Exact carrier and coefficient identifications with a specified coefficient blowup center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

local instance specifiedCarrierNoetherian (H : X.IdealSheafData) : IsLocallyNoetherian H.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian H.subschemeι

theorem exists_globalRetainedCoefficientTransform_specified_iso
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [IsIntegral H.subscheme] [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I)
    (K : H.subscheme.IdealSheafData) (hK : K ≠ ⊥) (hIK : I.comap H.subschemeι = K)
    (C : H.subscheme.IdealSheafData) (b : ℕ) :
    ∃ e : GlobalBlowup.Data.Construction.globalBlowup K hK ≅ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme,
      e.hom ≫ ((GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)) =
        GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ (H.subschemeι ≫ f) ∧
      (Transform.Construction.globalRetainedCoefficientTransform I H C hI b).comap e.hom = GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K C hK b.factorial := by
  subst K
  obtain ⟨e, hover, hcoeff⟩ := exists_globalRetainedCoefficientTransform_carrier_iso f I H hI hH hlocal hHI hK C b
  refine ⟨e, ?_, hcoeff⟩
  have h := congrArg (fun v => v ≫ H.subschemeι ≫ f) hover
  rw [Category.assoc e.hom, ← Category.assoc (Transform.Construction.globalControlledCarrierMap I H hI) H.subschemeι f,
    Transform.Construction.globalControlledCarrierMap_over, Category.assoc] at h
  exact h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Upper.Construction
