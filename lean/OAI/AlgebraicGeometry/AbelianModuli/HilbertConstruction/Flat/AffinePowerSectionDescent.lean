import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.AffineSectionSpanning
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.LinearCombinationNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Affine Power Section Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Ampleness after a flat surjective affine base change supplies pointwise nonvanishing power sections before base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.pointwise_power_sections_of_flat_affine_baseChange
    {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) [Flat g] [Surjective g]
    (L : Line.Bundles.LineBundle X) (hL : (L.pullback a).IsAmple) :
    ∀ x : X, ∃ (n : ℕ) (_ : 0 < n) (s : Line.Bundles.structureModule X ⟶ (L.tensorPower n).sheaf),
      x ∈ Ample.LineBundles.sectionNonvanishing s := by
  have : Surjective a := MorphismProperty.of_isPullback H.flip (inferInstance : Surjective g)
  intro x
  obtain ⟨y, hy⟩ := a.surjective x
  obtain ⟨n, hn, t, hyt, _⟩ := ((L.pullback a).isAmple_iff_tensorPower.mp hL).2 y
  let q := t ≫ (L.powerBaseChangeIso a n).inv
  have hyq : y ∈ Ample.LineBundles.sectionNonvanishing q :=
    (congrArg (fun U : P.Opens => y ∈ U)
      (Ample.Powers.sectionNonvanishing_comp_iso t (L.powerBaseChangeIso a n).symm)).mpr hyt
  obtain ⟨k, c, s, hq⟩ := HilbertConstruction.Flat.AffineSectionSpanning.flat_affinePullback_sections_spanned H (L.tensorPower n) q
  have hys : y ∈ Ample.LineBundles.sectionNonvanishing (∑ i, Scalar.SectionValues.scalarSection (b.appTop (c i)) (Ample.LineBundles.pullbackSection a (s i))) :=
    (congrArg (fun z => y ∈ Ample.LineBundles.sectionNonvanishing z) hq).mp hyq
  obtain ⟨i, _, hi⟩ := ((L.tensorPower n).pullback a).mem_sectionNonvanishing_sum Finset.univ
    (fun i => Scalar.SectionValues.scalarSection (b.appTop (c i)) (Ample.LineBundles.pullbackSection a (s i))) y hys
  have hiy := Scalar.SectionNonvanishing.scalarSection_nonvanishing_le ((L.tensorPower n).pullback a)
    (b.appTop (c i)) (Ample.LineBundles.pullbackSection a (s i)) hi
  have hix : a y ∈ Ample.LineBundles.sectionNonvanishing (s i) :=
    (congrArg (fun U : P.Opens => y ∈ U)
      (LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange a (L.tensorPower n) (s i))).mp hiy
  exact ⟨n, hn, s i, hy ▸ hix⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
