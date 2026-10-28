import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionCompletenessOpen

/-! # Section Fiber Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionFiberCriterion

noncomputable section

/-! For a proper flat line bundle over a Noetherian affine base,
universal completeness of a specified family is detected by the actual
section maps after every field-valued test. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def GeometricallyCompleteSectionFamily {S X T : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) {r : ℕ} (s : Fin r → (Line.Bundles.structureModule X ⟶ M)) (b : T ⟶ S) : Prop :=
  ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ T),
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination (pullback.snd f (a ≫ b)).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst f (a ≫ b))).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst f (a ≫ b)) (s i)))

theorem properFlat_universalSectionCompleteness_iff_geometric
    {S X T : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    {r : ℕ} (s : Fin r → (Line.Bundles.structureModule X ⟶ L.sheaf)) (b : T ⟶ S) :
    Universal.SectionCompletenessOpen.UniversallyCompleteSectionFamily f L.sheaf s b ↔ GeometricallyCompleteSectionFamily f L.sheaf s b := by
  constructor
  · intro h K _ a
    exact h (Spec (.of K)) a
  · intro h
    obtain ⟨V, hfield, hall⟩ := Universal.SectionCompletenessOpen.properFlat_exists_universalSectionCompletenessOpen_with_fields f L s
    apply (hall T b).mp
    rintro _ ⟨t, rfl⟩
    let q := T.fromSpecResidueField t
    let z : Spec (T.residueField t) := (⊥ : PrimeSpectrum (T.residueField t))
    have hq := (hfield (T.residueField t) (q ≫ b)).mpr (h (T.residueField t) q)
    have hz := hq ⟨z, rfl⟩
    change b (T.fromSpecResidueField t z) ∈ V at hz
    change b t ∈ V
    simpa only [Scheme.fromSpecResidueField_apply] using hz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionFiberCriterion
