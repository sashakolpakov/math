import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClassNaturality
import OAI.AlgebraicGeometry.Betti.GeometricClasses
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality
import OAI.AlgebraicTopology.DeRham.Comparison.RationalHodgeClasses

/-! # Image Naturality -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# The geometric cycle-class image under algebraic isomorphisms

The cycle map here is the new map constructed from actual fundamental-class
traces and Poincare duality. Its proved isomorphism square, together with the
actual equivalence of algebraic supports, transports its image. The Hodge
class comparison uses the independently proved pullback of pure-type forms.
-/

open _root_.CategoryTheory

variable {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}

/-- Actual singular pullback preserves and reflects the image of the
geometric fundamental-cycle class map. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_mem_geometricAlgebraicClasses_iff
    (e : V.toOver ≅ W.toOver) (p : ℕ) (a : W.rationalCohomology (p + p)) :
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p) a ∈ V.geometricAlgebraicClasses p ↔
      a ∈ W.geometricAlgebraicClasses p := by
  let t := CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv ℚ e p
  have natural (z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V p) :
      Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p) (W.geometricCycleClassMap p (t z)) =
        V.geometricCycleClassMap p z :=
    LinearMap.congr_fun (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_iso_naturality e p) z
  have hinj : Function.Injective (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p)) :=
    (asIso (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p))).toLinearEquiv.injective
  rw [V.mem_geometricAlgebraicClasses_iff, W.mem_geometricAlgebraicClasses_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨t z, hinj ((natural z).trans hz)⟩
  · rintro ⟨z, hz⟩
    refine ⟨t.symm z, ?_⟩
    calc
      V.geometricCycleClassMap p (t.symm z) =
          Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p)
            (W.geometricCycleClassMap p (t (t.symm z))) := (natural _).symm
      _ = Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p) a := by
        rw [t.apply_symm_apply, hz]

/-- The actual geometric algebraic submodule is the inverse image under
the genuine singular-cohomology pullback. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricAlgebraicClasses_comap (e : V.toOver ≅ W.toOver) (p : ℕ) :
    (V.geometricAlgebraicClasses p).comap (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p)).hom =
      W.geometricAlgebraicClasses p := by
  ext a
  exact Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_mem_geometricAlgebraicClasses_iff e p a

/-- Pullback also carries the whole geometric algebraic image onto the
geometric algebraic image of the isomorphic variety. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricAlgebraicClasses_map (e : V.toOver ≅ W.toOver) (p : ℕ) :
    (W.geometricAlgebraicClasses p).map (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p)).hom =
      V.geometricAlgebraicClasses p := by
  ext a
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_mem_geometricAlgebraicClasses_iff e p b).mpr hb
  · intro ha
    obtain ⟨b, rfl⟩ :=
      (asIso (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p))).toLinearEquiv.surjective a
    exact ⟨b, (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_mem_geometricAlgebraicClasses_iff e p b).mp ha, rfl⟩

/-- The exact rational Hodge containment for the new geometric class image
is invariant under an actual isomorphism over the complex base. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalHodgeClasses_le_geometricAlgebraicClasses_iff
    (e : V.toOver ≅ W.toOver) (p : ℕ) :
    V.rationalHodgeClasses p ≤ V.geometricAlgebraicClasses p ↔
      W.rationalHodgeClasses p ≤ W.geometricAlgebraicClasses p := by
  rw [V.rationalHodgeClasses_le_iff, W.rationalHodgeClasses_le_iff]
  constructor
  · intro h a ha
    apply (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_mem_geometricAlgebraicClasses_iff e p a).mp
    exact h _ (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_pullback e.hom p ha)
  · intro h a ha
    apply (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_mem_geometricAlgebraicClasses_iff e.symm p a).mp
    exact h _ (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_pullback e.inv p ha)

/-- The two defining conditions of a rational Hodge class outside the new
geometric algebraic image are preserved and reflected by pullback. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_not_geometric_algebraic_pullback_iff
    (e : V.toOver ≅ W.toOver) (p : ℕ) (a : W.rationalCohomology (p + p)) :
    (V.IsRationalHodgeClass p (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p) a) ∧
        Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p) a ∉ V.geometricAlgebraicClasses p) ↔
      (W.IsRationalHodgeClass p a ∧ a ∉ W.geometricAlgebraicClasses p) :=
  and_congr (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_pullback_iff e p a)
    (not_congr (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_mem_geometricAlgebraicClasses_iff e p a))

/-- Existence of a Hodge class outside the geometric cycle image is
likewise independent of the chosen algebraic presentation. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.exists_isRationalHodgeClass_not_geometric_algebraic_iff
    (e : V.toOver ≅ W.toOver) (p : ℕ) :
    (∃ a : V.rationalCohomology (p + p),
      V.IsRationalHodgeClass p a ∧ a ∉ V.geometricAlgebraicClasses p) ↔
    (∃ a : W.rationalCohomology (p + p),
      W.IsRationalHodgeClass p a ∧ a ∉ W.geometricAlgebraicClasses p) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.inv (p + p) a,
      (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_not_geometric_algebraic_pullback_iff e.symm p a).mpr ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p) a,
      (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_not_geometric_algebraic_pullback_iff e p a).mpr ha⟩

end

end OAI.AlgebraicGeometry
