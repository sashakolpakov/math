import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Immersion Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ImmersionComplexPoints

noncomputable section

/-!
# Field-valued points in the image of an immersion

A morphism surjective on stalks induces isomorphisms on residue fields. Hence
a field-valued point whose underlying point lies in its image lifts through
the morphism: transport the residue-field character through that isomorphism.
This also proves the exact image formula for ordinary relative complex points
of closed immersions, immersions, and preimmersions, without any finite-type
or algebraic-closedness assumption in the field-valued lifting theorem.

Only algebraic point sets occur here; no analytic topology is imported.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

section ResidueFields

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f]

/-- Surjectivity on stalks descends to surjectivity on the actual residue fields. -/
theorem residueFieldMap_surjective_of_surjectiveOnStalks (x : X) :
    Function.Surjective (f.residueFieldMap x) := by
  have h : Function.Surjective (f.stalkMap x ≫ X.residue x) :=
    (X.residue_surjective x).comp (f.stalkMap_surjective x)
  rw [← Scheme.residue_residueFieldMap f x] at h
  rw [ConcreteCategory.coe_comp] at h
  exact Function.Surjective.of_comp h

/-- The induced residue-field map is an actual isomorphism: injectivity comes
from its field domain and surjectivity from the stalk map. -/
def residueFieldIsoOfSurjectiveOnStalks (x : X) :
    Y.residueField (f x) ≅ X.residueField x :=
  (RingEquiv.ofBijective (f.residueFieldMap x).hom
    ⟨(f.residueFieldMap x).hom.injective,
      residueFieldMap_surjective_of_surjectiveOnStalks f x⟩).toCommRingCatIso

@[simp]
theorem residueFieldIsoOfSurjectiveOnStalks_hom (x : X) :
    (residueFieldIsoOfSurjectiveOnStalks f x).hom = f.residueFieldMap x := rfl

end ResidueFields

section FieldPoints

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- Every field-valued point with underlying point in the image lifts through
a morphism surjective on stalks. The residue-field character is transported
through the inverse of the actual residue-field map. -/
theorem surjectiveOnStalks_exists_fieldPoint_lift (f : X ⟶ Y)
    [SurjectiveOnStalks f] (p : Spec (.of K) ⟶ Y) (z : Spec (.of K))
    (hp : p z ∈ Set.range f) :
    ∃ q : Spec (.of K) ⟶ X, q ≫ f = p := by
  obtain ⟨⟨y, χ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective p
  change (Spec.map χ ≫ Y.fromSpecResidueField y) z ∈ Set.range f at hp
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at hp
  obtain ⟨x, hx⟩ := hp
  subst y
  let : IsIso (f.residueFieldMap x) :=
    (residueFieldIsoOfSurjectiveOnStalks f x).isIso_hom
  refine ⟨Spec.map (inv (f.residueFieldMap x) ≫ χ) ≫ X.fromSpecResidueField x, ?_⟩
  change _ = Spec.map χ ≫ Y.fromSpecResidueField (f x)
  rw [Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField x,
    ← Category.assoc, ← Spec.map_comp]
  simp

/-- The field-valued lift respects a prescribed base morphism automatically. -/
theorem surjectiveOnStalks_relativeFieldPoint_existsLift
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [SurjectiveOnStalks f.left]
    {b : Spec (.of K) ⟶ S} (p : Over.mk b ⟶ Y) (z : Spec (.of K))
    (hp : p.left z ∈ Set.range f.left) :
    ∃ q : Over.mk b ⟶ X, q ≫ f = p := by
  obtain ⟨q, hq⟩ := surjectiveOnStalks_exists_fieldPoint_lift f.left p.left z hp
  refine ⟨Over.homMk q ?_, ?_⟩
  · rw [← f.w, ← Category.assoc, hq]
    exact p.w
  · apply Over.OverMorphism.ext
    exact hq

/-- Exact image of the relative field-point map for a morphism surjective
on stalks. -/
theorem range_surjectiveOnStalks_relativeFieldPointMap
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [SurjectiveOnStalks f.left]
    (b : Spec (.of K) ⟶ S) (z : Spec (.of K)) :
    Set.range (fun q : Over.mk b ⟶ X => q ≫ f) =
      {p : Over.mk b ⟶ Y | p.left z ∈ Set.range f.left} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.left z, (Scheme.Hom.comp_apply q.left f.left z).symm⟩
  · exact fun hp => surjectiveOnStalks_relativeFieldPoint_existsLift f p z hp

/-- For a preimmersion the relative field-valued lift is unique. -/
theorem preimmersion_relativeFieldPoint_existsUnique
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [IsPreimmersion f.left]
    {b : Spec (.of K) ⟶ S} (p : Over.mk b ⟶ Y) (z : Spec (.of K))
    (hp : p.left z ∈ Set.range f.left) :
    ∃! q : Over.mk b ⟶ X, q ≫ f = p := by
  let : Mono f := Over.mono_of_mono_left f
  obtain ⟨q, hq⟩ := surjectiveOnStalks_relativeFieldPoint_existsLift f p z hp
  refine ⟨q, hq, ?_⟩
  intro r hr
  exact (cancel_mono f).mp (hr.trans hq.symm)

end FieldPoints

variable {X Y : Over ProjectiveSpace.complexBase}

/-- The precise image of the ordinary relative complex-point map, stated
without importing or changing its analytic topology. -/
theorem range_surjectiveOnStalks_complexPointMap (f : X ⟶ Y)
    [SurjectiveOnStalks f.left] :
    Set.range (fun q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X => q ≫ f) =
      {p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Y |
        p.left (⊥ : PrimeSpectrum ℂ) ∈ Set.range f.left} :=
  range_surjectiveOnStalks_relativeFieldPointMap f (𝟙 ProjectiveSpace.complexBase)
    (⊥ : PrimeSpectrum ℂ)

/-- Closed immersions have exactly the complex points prescribed by their
underlying scheme image. -/
theorem range_closedImmersion_complexPointMap (f : X ⟶ Y)
    [IsClosedImmersion f.left] :
    Set.range (fun q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X => q ≫ f) =
      {p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Y |
        p.left (⊥ : PrimeSpectrum ℂ) ∈ Set.range f.left} :=
  range_surjectiveOnStalks_complexPointMap f

/-- The same image characterization holds for every scheme immersion. -/
theorem range_immersion_complexPointMap (f : X ⟶ Y) [IsImmersion f.left] :
    Set.range (fun q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X => q ≫ f) =
      {p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Y |
        p.left (⊥ : PrimeSpectrum ℂ) ∈ Set.range f.left} :=
  range_surjectiveOnStalks_complexPointMap f

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ImmersionComplexPoints
