import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.PointSectionAvoidance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.RingSectionBasis

/-! # Finite Point Section Avoidance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FinitePointSectionAvoidance

noncomputable section

/-! A section can vanish at one prescribed point while avoiding a finite
family of other points, provided each point can be avoided separately
with the same vanishing constraint. This is finite subspace avoidance
inside the actual space of sections vanishing at the prescribed point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X)

theorem sectionVanishingSubmodule_coefficient_mem (x : X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf s ∈ HilbertConstruction.Finite.PointSectionAvoidance.sectionVanishingSubmodule p L x ↔
      x ∉ Ample.LineBundles.sectionNonvanishing s := by
  let e := Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf
  change x ∉ Ample.LineBundles.sectionNonvanishing (e.symm (e s)) ↔ x ∉ Ample.LineBundles.sectionNonvanishing s
  rw [e.symm_apply_apply]

include p in
theorem exists_section_vanishing_and_nonvanishing_at_finite_points [Infinite K]
    {ι : Type v} [Finite ι] (z : X) (x : ι → X)
    (h : ∀ i, ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf,
      z ∉ Ample.LineBundles.sectionNonvanishing s ∧ x i ∈ Ample.LineBundles.sectionNonvanishing s) :
    ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf,
      z ∉ Ample.LineBundles.sectionNonvanishing s ∧ ∀ i, x i ∈ Ample.LineBundles.sectionNonvanishing s := by
  let e := Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf
  let W := HilbertConstruction.Finite.PointSectionAvoidance.sectionVanishingSubmodule p L z
  let Q (i : ι) : Submodule K W := (HilbertConstruction.Finite.PointSectionAvoidance.sectionVanishingSubmodule p L (x i)).comap W.subtype
  have hQ (i : ι) : Q i ≠ ⊤ := by
    obtain ⟨s, hz, hx⟩ := h i
    let v : W := ⟨e s, (sectionVanishingSubmodule_coefficient_mem p L z s).mpr hz⟩
    intro htop
    have hv : v ∈ Q i := by rw [htop]; trivial
    have hv' : e s ∈ HilbertConstruction.Finite.PointSectionAvoidance.sectionVanishingSubmodule p L (x i) := hv
    exact (sectionVanishingSubmodule_coefficient_mem p L (x i) s).mp hv' hx
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top Q hQ
  refine ⟨e.symm v.val, ?_, ?_⟩
  · change v.val ∈ W
    exact v.property
  · intro i
    apply Classical.not_not.mp
    change ¬ (v ∈ Q i)
    exact hv i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FinitePointSectionAvoidance
