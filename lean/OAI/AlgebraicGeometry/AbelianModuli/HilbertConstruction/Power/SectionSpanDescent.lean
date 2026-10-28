import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.LinearCombinationNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointwiseGeneratingPower
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Section Span Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! If sections of pulled-back positive powers are spanned by pulled-back sections, ampleness upstairs gives pointwise nonvanishing power sections downstairs. The section-spanning property is an explicit hypothesis to be supplied by a base-change theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.pointwise_power_sections_of_surjective_spanning_pullback
    {K : Type u} [Field K] {X Y : Scheme.{u}} (a : Y ⟶ X) [Surjective a]
    (p : Y ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) (hL : (L.pullback a).IsAmple)
    (hspan : ∀ (n : ℕ) (t : Line.Bundles.structureModule Y ⟶ ((L.tensorPower n).pullback a).sheaf),
      ∃ (k : ℕ) (c : Fin k → K) (s : Fin k → (Line.Bundles.structureModule X ⟶ (L.tensorPower n).sheaf)),
        t = ∑ i, Coefficient.ScalarSections.coefficientScalarSection p (c i) (Ample.LineBundles.pullbackSection a (s i))) :
    ∀ x : X, ∃ (n : ℕ) (_ : 0 < n) (s : Line.Bundles.structureModule X ⟶ (L.tensorPower n).sheaf),
      x ∈ Ample.LineBundles.sectionNonvanishing s := by
  intro x
  obtain ⟨y, hy⟩ := a.surjective x
  obtain ⟨n, hn, t, hyt, _⟩ := ((L.pullback a).isAmple_iff_tensorPower.mp hL).2 y
  let q := t ≫ (L.powerBaseChangeIso a n).inv
  have hyq : y ∈ Ample.LineBundles.sectionNonvanishing q :=
    (congrArg (fun U : Y.Opens => y ∈ U)
      (Ample.Powers.sectionNonvanishing_comp_iso t (L.powerBaseChangeIso a n).symm)).mpr hyt
  obtain ⟨k, c, s, hq⟩ := hspan n q
  have hys : y ∈ Ample.LineBundles.sectionNonvanishing (∑ i, Coefficient.ScalarSections.coefficientScalarSection p (c i) (Ample.LineBundles.pullbackSection a (s i))) :=
    (congrArg (fun z => y ∈ Ample.LineBundles.sectionNonvanishing z) hq).mp hyq
  obtain ⟨i, _, hi⟩ := Section.LinearCombinationNonvanishing.pulledBack_linearCombination_nonvanishing a p (L.tensorPower n) Finset.univ c s y hys
  exact ⟨n, hn, s i, hy ▸ hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
