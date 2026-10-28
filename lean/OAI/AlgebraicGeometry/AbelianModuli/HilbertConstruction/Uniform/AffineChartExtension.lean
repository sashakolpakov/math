import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.PowerNumerators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransport

/-! # Affine Chart Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.AffineChartExtension

noncomputable section

/-! Affine-chart extensions in every sufficiently large original tensor power. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {L : Y.Modules}

/-- Compare the ratio after power transport with the ratio in the local power. -/
theorem frameCoordinate_transportPowerSection_power (n : ℕ) (h : Z ⟶ X) [IsOpenImmersion h]
    (s : Line.Bundles.structureModule Y ⟶ L)
    (t : Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj L) n)
    [IsIso (Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f s))] :
    letI := Power.SectionTransport.iteratedPullback_power_isIso f n h s
    letI := Power.Nonvanishing.tensorPowerSection_pullback_isIso h (Ample.LineBundles.pullbackSection f s) n
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n)))
      (Ample.LineBundles.pullbackSection h (Power.SectionTransport.transportPowerSection f n t)) =
        Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection h (TensorPower.Maps.tensorPowerSection (Ample.LineBundles.pullbackSection f s) n))
          (Ample.LineBundles.pullbackSection h t) := by
  let d := TensorPower.Maps.tensorPowerSection (Ample.LineBundles.pullbackSection f s) n
  have hd : IsIso (Ample.LineBundles.pullbackSection h d) :=
    Power.Nonvanishing.tensorPowerSection_pullback_isIso h (Ample.LineBundles.pullbackSection f s) n
  have hc : IsIso (Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n))) :=
    Power.SectionTransport.iteratedPullback_power_isIso f n h s
  have htr : IsIso (Ample.LineBundles.pullbackSection h (Power.SectionTransport.transportPowerSection f n d)) :=
    @Section.FrameTransport.pullbackSection_frameTransport_isIso Z X h _ _
      (Power.SectionTransport.tensorPowerPullbackSourceIso f n) ((Local.PowerCoordinates.tensorPowerPullbackNatIso f n).app L) d hd
  have heq : Ample.LineBundles.pullbackSection h (Power.SectionTransport.transportPowerSection f n d) =
      Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n)) :=
    congrArg (Ample.LineBundles.pullbackSection h) (Power.SectionTransport.transportPowerSection_power f n s)
  have hcoords := @Frame.FrameRestriction.frameCoordinate_congr Z _ _ _
    (Ample.LineBundles.pullbackSection h (Power.SectionTransport.transportPowerSection f n t)) _ htr hc heq rfl
  exact hcoords.symm.trans (Power.SectionTransport.frameCoordinate_transportPowerSection f n h (L := L) d t)

/-- On an affine framed chart, extension into the original tensor powers works
in every degree beyond a positive threshold. -/
theorem affine_chart_section_extension_eventually [IsAffine X]
    (e : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) [IsIso e]
    (s : Line.Bundles.structureModule Y ⟶ L)
    (r : Γ((Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).toScheme, ⊤)) :
    ∃ (n : ℕ) (_ : 0 < n), ∀ m : ℕ, n ≤ m →
      ∃ t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L m),
        letI := Power.SectionTransport.iteratedPullback_power_isIso f m (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι s
        Frame.Coordinates.frameCoordinate
          (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι
            (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s m)))
          (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι t) = r := by
  obtain ⟨n, hn, hn'⟩ := Framed.PowerNumerators.framed_affine_section_extension_eventually e (Ample.LineBundles.pullbackSection f s) r
  refine ⟨n, hn, fun m hm => ?_⟩
  obtain ⟨t, ht⟩ := hn' m hm
  refine ⟨Power.SectionTransport.transportPowerSection f m t, ?_⟩
  exact (frameCoordinate_transportPowerSection_power f m
    (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι s t).trans ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.AffineChartExtension
