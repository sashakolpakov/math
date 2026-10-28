import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.TransitionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections

/-! # Affine Annihilation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineAnnihilation

noncomputable section

/-!
On an affine framed chart, differences vanishing on `D(s)` are killed by
iterated multiplication by `s`. This is the local overlap-annihilation step
for gluing power-section extensions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L : X.Modules}

theorem frameCoordinate_injective (e : Line.Bundles.structureModule X ⟶ L) [IsIso e] :
    Function.Injective (fun t : Line.Bundles.structureModule X ⟶ L => Frame.Coordinates.frameCoordinate e t) := by
  intro s t h
  have he : Frame.Coordinates.frameCoordinateEnd e s = Frame.Coordinates.frameCoordinateEnd e t :=
    Global.Sections.structureModuleEndValue_injective X h
  exact (Frame.Coordinates.frameCoordinateEnd_frame e s).symm.trans
    ((congrArg (fun z : End (Line.Bundles.structureModule X) => z ≫ e) he).trans (Frame.Coordinates.frameCoordinateEnd_frame e t))

theorem frameCoordinate_eq_zero_iff (e : Line.Bundles.structureModule X ⟶ L) [IsIso e]
    (t : Line.Bundles.structureModule X ⟶ L) : Frame.Coordinates.frameCoordinate e t = 0 ↔ t = 0 :=
  ⟨fun h => frameCoordinate_injective e (h.trans (ZeroSections.frameCoordinate_zero e).symm),
    fun h => h ▸ ZeroSections.frameCoordinate_zero e⟩

/-- A numerator that vanishes on `D(s)` becomes zero after multiplication by
a suitable power of `s`, on an affine scheme with a global line-bundle frame. -/
theorem framed_affine_power_annihilation [IsAffine X]
    (e s : Line.Bundles.structureModule X ⟶ L) [IsIso e] (n : ℕ)
    (t : Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule L n)
    (ht : Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t = 0) :
    ∃ m : ℕ, t ≫ Power.SectionTransitions.powerSectionTransition s n m = 0 := by
  let D := Ample.LineBundles.sectionNonvanishing s
  let b := Frame.Coordinates.frameCoordinate (TensorPower.Maps.tensorPowerSection e n) t
  let c := Frame.Coordinates.frameCoordinate e s
  let a := D.ι.appTop.hom
  let := a.toAlgebra
  have : IsLocalization.Away c Γ(D.toScheme, ⊤) := AffineLocalization.framed_nonvanishing_localization e s
  have hb : a b = 0 :=
    (Frame.FrameRestriction.frameCoordinate_pullback D.ι (TensorPower.Maps.tensorPowerSection e n) t).symm.trans
      ((congrArg (fun z : Line.Bundles.structureModule D.toScheme ⟶
          (Scheme.Modules.pullback D.ι).obj (TensorPower.PowerSheaf.tensorPowerModule L n) =>
        Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection D.ι (TensorPower.Maps.tensorPowerSection e n)) z) ht).trans
          (ZeroSections.frameCoordinate_zero (Ample.LineBundles.pullbackSection D.ι (TensorPower.Maps.tensorPowerSection e n))))
  obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers c) Γ(D.toScheme, ⊤) b).mp hb
  refine ⟨m, (frameCoordinate_eq_zero_iff (TensorPower.Maps.tensorPowerSection e (n + m)) _).mp ?_⟩
  exact (Power.TransitionCoordinates.frameCoordinate_powerSectionTransition_frame e s n m t).trans
    ((mul_comm b (c ^ m)).trans hm)

/-- Two local numerators agreeing on `D(s)` agree everywhere after a common
increase in degree, on an affine scheme with a global line-bundle frame. -/
theorem framed_affine_power_equality [IsAffine X]
    (e s : Line.Bundles.structureModule X ⟶ L) [IsIso e] (n : ℕ)
    (t t' : Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule L n)
    (ht : Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t =
      Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t') :
    ∃ m : ℕ, t ≫ Power.SectionTransitions.powerSectionTransition s n m = t' ≫ Power.SectionTransitions.powerSectionTransition s n m := by
  have hsub : Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι (t - t') =
      Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t - Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t' := by
    simp only [Ample.LineBundles.pullbackSection, Functor.map_sub, Preadditive.comp_sub]
  obtain ⟨m, hm⟩ := framed_affine_power_annihilation e s n (t - t')
    (hsub.trans (by rw [ht, sub_self]))
  exact ⟨m, sub_eq_zero.mp ((Preadditive.sub_comp t t' _).symm.trans hm)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineAnnihilation
