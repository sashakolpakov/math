import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothHypersurfaceBlowupIso
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.CoefficientTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ZeroCenter

/-! # Nonzero Persistence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.NonzeroPersistence.Construction

noncomputable section

/-! A nonzero coefficient ideal prevents collapse of the coefficient carrier through permissible blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem coefficient_nonzero_center_pullback_ne_bot
    {X : Scheme} [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I J H : X.IdealSheafData) [Smooth (H.subschemeι ≫ f)] (b : ℕ) (hb : 0 < b)
    (hp : J ≤ I ^ b) (hC : CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι ≠ ⊥) :
    I.comap H.subschemeι ≠ ⊥ := by
  intro hz
  have hi : I ≤ H := (ZeroCenter.Construction.idealSheaf_comap_subscheme_eq_bot_iff I H).mp hz
  exact hC ((ZeroCenter.Construction.smoothCoefficientIdealSheaf_eq_bot_iff f J H b hb).mpr
    (hp.trans (pow_le_pow_left' hi b)))

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

local instance (H : X.IdealSheafData) : IsLocallyNoetherian H.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian H.subschemeι

/-- Nonzero coefficients stay nonzero on the actual smooth controlled
hypersurface, so the same carrier construction can be used at the next step. -/
theorem globalBlowup_smooth_hypersurface_coefficient_ne_bot
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I J H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [IsIntegral H.subscheme] [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I) (b : ℕ) (hb : 0 < b)
    (hp : J ≤ I ^ b) (hC : CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι ≠ ⊥) :
    letI : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
    CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) b (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι ≠ ⊥ := by
  let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
  have hIH := coefficient_nonzero_center_pullback_ne_bot f I J H b hb hp hC
  obtain ⟨e, he, _⟩ := Global.SmoothHypersurfaceBlowupIso.Construction.globalBlowup_smooth_hypersurface_iso f I H hI hH hlocal hHI hIH
  intro hz
  have hz' := congrArg (fun C : (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subscheme.IdealSheafData =>
    C.comap e.hom) hz
  rw [CoefficientSheaf.Construction.smoothCoefficientIdealSheaf_comap, he, Scheme.IdealSheafData.comap_bot] at hz'
  have hbound := CoefficientTransform.Construction.globalBlowup_coefficient_transform_le f H.subschemeι I J hI hIH b hp
  rw [hz'] at hbound
  exact GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot (I.comap H.subschemeι)
    (CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι) hIH b.factorial hC (le_bot_iff.mp hbound)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.NonzeroPersistence.Construction
