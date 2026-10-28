import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalCoefficient
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IsoCoefficient

/-! # Generic Coefficient Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericCoefficientIso.Cycles

noncomputable section

/-! # LineBundleCycles: generic coefficients of actual sections transform by the constructed sheaf-isomorphism coefficient -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] {L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X} (e : L.sheaf ≅ M.sheaf)

theorem genericSectionCoefficient_iso_on_reference (U : X.Opens) [Nonempty U]
    (hU : U ≤ IsoCoefficient.Cycles.lineBundleIsoReferenceOpen L M) (s : Γ(L.sheaf, U)) :
    M.genericSectionCoefficient U (e.hom.app U s) =
      (IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient e).val * L.genericSectionCoefficient U s := by
  rw [M.genericSectionCoefficient_eq_local (genericPoint X) U (hU.trans inf_le_right),
    L.genericSectionCoefficient_eq_local (genericPoint X) U (hU.trans inf_le_left)]
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient
  rw [L.rationalSectionCoordinate_reference, M.rationalSectionCoordinate_reference]
  simp only [Units.val_one, div_one]
  rw [IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient_on_open e U hU]
  change X.germToFunctionField U (M.sectionFrame (genericPoint X) U (hU.trans inf_le_right) (e.hom.app U s)) =
    X.germToFunctionField U (IsoFrames.Cycles.lineBundleIsoTransition e (genericPoint X) (genericPoint X) U
      (hU.trans inf_le_left) (hU.trans inf_le_right)).val *
        X.germToFunctionField U (L.sectionFrame (genericPoint X) U (hU.trans inf_le_left) s)
  rw [← map_mul]
  exact congrArg (X.germToFunctionField U)
    (FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_coordinates
      (IsoFrames.Cycles.transportedSectionFrame e (genericPoint X) U (hU.trans inf_le_right))
      (L.sectionFrame (genericPoint X) U (hU.trans inf_le_left)) s)

theorem genericSectionCoefficient_iso (U : X.Opens) [Nonempty U] (s : Γ(L.sheaf, U)) :
    M.genericSectionCoefficient U (e.hom.app U s) =
      (IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient e).val * L.genericSectionCoefficient U s := by
  let V := U ⊓ IsoCoefficient.Cycles.lineBundleIsoReferenceOpen L M
  let : Nonempty V := ⟨⟨genericPoint X,
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›),
    L.mem_trivializingOpen (genericPoint X), M.mem_trivializingOpen (genericPoint X)⟩⟩
  have hVU : V ≤ U := inf_le_left
  have hn := ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality (homOfLE hVU).op) s
  have hr := M.genericSectionCoefficient_restrict hVU (e.hom.app U s)
  calc
    M.genericSectionCoefficient U (e.hom.app U s) =
        M.genericSectionCoefficient V (e.hom.app V (L.sheaf.presheaf.map (homOfLE hVU).op s)) :=
      hr.symm.trans (congrArg (M.genericSectionCoefficient V) hn.symm)
    _ = (IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient e).val *
        L.genericSectionCoefficient V (L.sheaf.presheaf.map (homOfLE hVU).op s) :=
      genericSectionCoefficient_iso_on_reference e V inf_le_right _
    _ = _ := congrArg (fun a => (IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient e).val * a)
      (L.genericSectionCoefficient_restrict hVU s)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericCoefficientIso.Cycles
