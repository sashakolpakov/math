import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothHypersurfaceBlowupIso
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.CoefficientTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceHypersurface

/-! # Hypersurface Coefficient -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.HypersurfaceCoefficient.Construction

noncomputable section

/-! Retained native coefficient ideals and maximal contact on the actual controlled hypersurface. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

local instance (H : X.IdealSheafData) : IsLocallyNoetherian H.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian H.subschemeι

local instance (I H : X.IdealSheafData) (hI : I ≠ ⊥) :
    IsLocallyNoetherian (Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian (Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι

def globalHypersurfaceCoefficientTransform
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I J H : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) :
    (Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme.IdealSheafData :=
  Ideal.Construction.controlledIdealSheaf (I.comap H.subschemeι) (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι)
    b.factorial (ClosedTransformMap.Construction.closedTransformMap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) H (Ideal.Construction.globalBlowupControlledIdeal I H hI 1)
      (Ideal.Construction.totalIdeal_le_controlledIdealSheaf I H 1 (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)))

/-- The actual coefficient transform on the native transformed hypersurface
retains the exact factorial control and the intrinsic coefficient upper bound. -/
theorem globalHypersurfaceCoefficientTransform_le
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I J H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [IsIntegral H.subscheme] [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I) (hIH : I.comap H.subschemeι ≠ ⊥)
    (b : ℕ) (hp : J ≤ I ^ b) :
    letI : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
    globalHypersurfaceCoefficientTransform f I J H hI b ≤
      GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (Ideal.Construction.globalBlowupControlledIdeal I J hI b) b (Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι := by
  let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
  obtain ⟨e, he, heover⟩ := Global.SmoothHypersurfaceBlowupIso.Construction.globalBlowup_smooth_hypersurface_iso f I H hI hH hlocal hHI hIH
  apply (Affine.IdealChartDescent.Construction.idealSheaf_comap_le_iff_isIso _ _ e.hom).mp
  rw [globalHypersurfaceCoefficientTransform, Ideal.Construction.controlledIdealSheaf_comap_open, heover,
    GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf_comap, he]
  exact GlobalCoefficient.CoefficientTransform.Construction.globalBlowup_coefficient_transform_le f H.subschemeι I J hI hIH b hp

/-- The embedded intrinsic carrier remains a hypersurface of maximal contact
for the transformed marked ideal. -/
theorem globalBlowupMap_smooth_hypersurface_tangent_le
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I J H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [IsIntegral H.subscheme] [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I) (hIH : I.comap H.subschemeι ≠ ⊥)
    (n : ℕ) (hp : J ≤ I ^ (n + 1)) (ht : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) :
    letI : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
    (GlobalBlowup.FunctorialMap.Construction.globalBlowupMap H.subschemeι I hI hIH).ker ≤
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n := by
  let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
  rw [Global.SmoothHypersurfaceBlowupIso.Construction.globalBlowupMap_kernel_eq_smooth_hypersurface_controlled f I H hI hH hlocal hHI hIH]
  exact Global.SequenceHypersurface.Construction.globalBlowup_hypersurface_tangent_le f I J H hI n hp ht

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.HypersurfaceCoefficient.Construction
