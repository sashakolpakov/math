import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GeneratedHolomorphicFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonGeneratedTwist
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup

/-! # Holomorphic Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicFaithfulness

noncomputable section

/-! Equality of the original native holomorphic classes detects an
actual algebraic line-sheaf isomorphism on a smooth projective variety.
The proof uses a common generated twist, explicit projective comparison
coordinates, holomorphic-graph algebraization, and regular-unit gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance nativeHolomorphicFaithfulness_picardGroup :
    CommGroup (Quotient (HilbertConstruction.Line.Bundles.LineBundle.isoSetoid V.carrier)) :=
  Picard.Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup V.carrier

local instance nativeHolomorphicFaithfulness_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of V.analyticSpace)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace) 1

theorem lineBundles_iso_of_nativeHolomorphicClass_eq (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier)
    (he : HolomorphicLineClass.nativeHolomorphicLineClass V L = HolomorphicLineClass.nativeHolomorphicLineClass V K) :
    Nonempty (L.sheaf ≅ K.sheaf) := by
  obtain ⟨H, hL, hK⟩ := CommonGeneratedTwist.exists_common_generated_twist V L K
  obtain ⟨n, s, hs⟩ := CommonGeneratedTwist.finiteGlobalGenerators_numbered_sections V (L.tensor H) hL
  obtain ⟨m, t, ht⟩ := CommonGeneratedTwist.finiteGlobalGenerators_numbered_sections V (K.tensor H) hK
  have hLH : HolomorphicLineClass.nativeHolomorphicLineClass V (L.tensor H) = HolomorphicLineClass.nativeHolomorphicLineClass V (K.tensor H) :=
    (HolomorphicTensor.nativeHolomorphicLineClass_tensor V L H).trans
      ((congrArg (fun x => x + HolomorphicLineClass.nativeHolomorphicLineClass V H) he).trans
        (HolomorphicTensor.nativeHolomorphicLineClass_tensor V K H).symm)
  obtain ⟨e⟩ := GeneratedHolomorphicFaithfulness.generatedLineBundles_iso_of_holomorphicClass_eq V (L.tensor H) (K.tensor H) s t hs ht hLH
  have hc : HilbertConstruction.Line.Bundles.LineBundle.classOf L * HilbertConstruction.Line.Bundles.LineBundle.classOf H =
      HilbertConstruction.Line.Bundles.LineBundle.classOf K * HilbertConstruction.Line.Bundles.LineBundle.classOf H := Quotient.sound ⟨e⟩
  exact Quotient.exact (mul_right_cancel hc)

theorem nativeHolomorphicLineClass_eq_iff (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier) :
    HolomorphicLineClass.nativeHolomorphicLineClass V L = HolomorphicLineClass.nativeHolomorphicLineClass V K ↔ Nonempty (L.sheaf ≅ K.sheaf) :=
  ⟨lineBundles_iso_of_nativeHolomorphicClass_eq V L K, fun ⟨e⟩ => HolomorphicIsoClass.nativeHolomorphicLineClass_iso V L K e⟩

theorem nativeHolomorphicPicardClass_injective : Function.Injective (HolomorphicIsoClass.nativeHolomorphicPicardClass V) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h L =>
    induction b using Quotient.inductionOn with
    | h K =>
      intro h
      exact Quotient.sound (lineBundles_iso_of_nativeHolomorphicClass_eq V L K h)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicFaithfulness
