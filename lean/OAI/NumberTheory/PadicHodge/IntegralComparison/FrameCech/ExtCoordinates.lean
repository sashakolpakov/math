import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Ext

/-! # Ext Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtCoordinates

noncomputable section

/-! The actual Ext-to-Čech comparison evaluates an original degree-zero Ext class in its native section coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  (H : Sheaf J (ModuleCat.{max u v} R))

theorem coordinate_mk (n : ℕ) (t : Fin (n + 1) → ι)
    (f : (CoveringPresentationResolution.complex J R F).X n ⟶ H) :
    Differential.coordinate F R H.obj n t
      (((FrameCech.Ext.Comparison.comparison F R J H).hom.f n (Abelian.Ext.mk₀ f)).down) =
        Presentation.ResolutionCoordinates.sheaf F R n J H f t := by
  change Differential.coordinate F R H.obj n t
    ((SectionIso.component F R J H n).hom
      (IntegralComparison.Ext.ZeroContravariantSections.equivalence R H ((CoveringPresentationResolution.complex J R F).X n)
        (Abelian.Ext.mk₀ f)).down) = _
  have h := congrArg ULift.down (IntegralComparison.Ext.ZeroContravariantSections.equivalence_mk R H
    ((CoveringPresentationResolution.complex J R F).X n) f)
  exact (congrArg (fun a => Differential.coordinate F R H.obj n t
    ((SectionIso.component F R J H n).hom a)) h).trans
      (SectionIso.component_coordinate F R J H n f t)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtCoordinates
