import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Etale Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.EtaleDetection.Construction

/-!
Fieldwise detection for the relative IsogenyQuotient construction. Equality of maps
to an etale scheme can be checked on residue fields without any reducedness
assumption on the source. Applied to the target's finite etale n-torsion,
this gives the integrality test required for relative polarization descent.
The actual subgroup and torsion definitions come from TorsionQuotient's repaired API.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

section Detection

variable {S : Scheme.{u}} {X Y : Over S}

set_option backward.isDefEq.respectTransparency false in
/-- An unramified target makes the equality locus of two maps open. -/
theorem equalizer_openImmersion
    [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom]
    (f g : X ⟶ Y) : IsOpenImmersion (equalizer.ι f g).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget S)).flip ?_
  change IsOpenImmersion (prod.lift (𝟙 Y) (𝟙 Y)).left
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
  ext1 <;> simp [← Over.comp_left]

/-- Maps to an etale target are determined by their values on residue
fields, including when the source scheme has nilpotents. -/
theorem etale_ext_of_residue_fields
    [Etale Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : X.left,
      X.left.fromSpecResidueField x ≫ f.left =
        X.left.fromSpecResidueField x ≫ g.left) : f = g := by
  have hopen : IsOpenImmersion (equalizer.ι f g).left := equalizer_openImmersion f g
  have hsurj : Surjective (equalizer.ι f g).left := by
    constructor
    intro x
    let T : Over S := Over.mk (X.left.fromSpecResidueField x ≫ X.hom)
    let p : T ⟶ X := Over.homMk (X.left.fromSpecResidueField x) rfl
    have hp : p ≫ f = p ≫ g := Over.OverMorphism.ext (h x)
    let l := equalizer.lift p hp
    let x₀ : Spec (X.left.residueField x) := default
    refine ⟨l.left x₀, ?_⟩
    change (l.left ≫ (equalizer.ι f g).left) x₀ = x
    rw [← Over.comp_left, equalizer.lift_ι]
    exact X.left.fromSpecResidueField_apply x x₀
  have : IsIso (equalizer.ι f g).left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hopen, hsurj⟩
  apply Over.OverMorphism.ext
  apply (cancel_epi (equalizer.ι f g).left).mp
  exact congrArg (fun a => a.left) (equalizer.condition f g)

/-- A version whose hypotheses are stated on arbitrary field-valued
points, as in the field-level polarization descent input. -/
theorem etale_ext_of_field_points
    [Etale Y.hom] (f g : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
      (x : Over.mk s ⟶ X), x ≫ f = x ≫ g) : f = g := by
  apply etale_ext_of_residue_fields f g
  intro x
  exact congrArg (fun a => a.left)
    (h (X.left.residueField x) (X.left.fromSpecResidueField x ≫ X.hom)
      (Over.homMk (X.left.fromSpecResidueField x) rfl))

end Detection

variable {S : Scheme.{u}} {B D H : Over S} [GrpObj B] [GrpObj D]

/-- A homomorphism sends n-torsion to n-torsion. -/
noncomputable def mapTorsion (f : B ⟶ D) [IsMonHom f] (n : ℕ) :
    TorsionQuotient.SubgroupFunctor.torsionScheme B n ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme D n :=
  TorsionQuotient.SubgroupFunctor.torsionLift n (TorsionQuotient.SubgroupFunctor.torsionι B n ≫ f) (by
    rw [← MonObj.pow_comp]
    have hi : TorsionQuotient.SubgroupFunctor.torsionι B n ^ n = 1 :=
      (TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (TorsionQuotient.SubgroupFunctor.torsionι B n)).mp
        ⟨𝟙 _, Category.id_comp _⟩
    rw [hi, MonObj.one_comp])

@[simp]
theorem mapTorsion_ι (f : B ⟶ D) [IsMonHom f] (n : ℕ) :
    mapTorsion f n ≫ TorsionQuotient.SubgroupFunctor.torsionι D n = TorsionQuotient.SubgroupFunctor.torsionι B n ≫ f :=
  TorsionQuotient.SubgroupFunctor.torsionLift_ι _ _ _

/-- Fieldwise vanishing on an n-torsion subgroup implies global vanishing
as a scheme morphism. Only the target n-torsion needs to be etale. -/
theorem torsion_vanishing_of_field_points
    (n : ℕ) (i : H ⟶ B) (hi : i ^ n = 1)
    (f : B ⟶ D) [IsMonHom f]
    (h_TorsionQuotient : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme D n).hom)
    (h_fieldwise : ∀ (K : Type u) [Field K]
      (s : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk s ⟶ H),
        (x ≫ i) ≫ f = 1) : i ≫ f = 1 := by
  let a := TorsionQuotient.SubgroupFunctor.torsionLift n (i ≫ f) (by
    rw [← MonObj.pow_comp, hi, MonObj.one_comp])
  let b := TorsionQuotient.SubgroupFunctor.torsionLift n (1 : H ⟶ D) (one_pow n)
  have : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme D n).hom := h_TorsionQuotient
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι D n) := by
    unfold TorsionQuotient.SubgroupFunctor.torsionι
    exact equalizer.ι_mono (f := (𝟙 D : D ⟶ D) ^ n) (g := (1 : D ⟶ D))
  have hab : a = b := by
    apply etale_ext_of_field_points
    intro K hK s x
    apply (cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι D n)).mp
    simp only [Category.assoc, a, b, TorsionQuotient.SubgroupFunctor.torsionLift_ι, MonObj.comp_one]
    simpa only [Category.assoc] using h_fieldwise K s x
  have h := congrArg (fun t => t ≫ TorsionQuotient.SubgroupFunctor.torsionι D n) hab
  simpa only [a, b, TorsionQuotient.SubgroupFunctor.torsionLift_ι] using h

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.EtaleDetection.Construction
