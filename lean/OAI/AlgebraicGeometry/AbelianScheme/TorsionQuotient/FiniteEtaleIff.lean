import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteEtaleLift
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points

/-! # Finite Etale Iff -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteEtaleIff.FiniteEtaleImage

/-! The clopen scheme image of a morphism between finite étale schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X Y : Over S}
variable [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom]
variable (f : X ⟶ Y)

noncomputable def locus : Y.left.Opens := by
  have : Etale f.left := (FiniteEtaleLift.FiniteEtaleLimits.hom_finite_etale f).2
  exact ⟨Set.range f.left, f.left.isOpenMap.isOpen_range⟩

theorem locus_closed : IsClosed (locus f : Set Y.left) := by
  have : IsFinite f.left := (FiniteEtaleLift.FiniteEtaleLimits.hom_finite_etale f).1
  exact f.left.isClosedMap.isClosed_range

noncomputable def image : Over S := Over.mk ((locus f).ι ≫ Y.hom)

noncomputable def inclusion : image f ⟶ Y := Over.homMk (locus f).ι rfl

instance inclusion_open : IsOpenImmersion (inclusion f).left :=
  inferInstanceAs (IsOpenImmersion (locus f).ι)

instance inclusion_closed : IsClosedImmersion (inclusion f).left := by
  apply IsClosedImmersion.of_isPreimmersion
  change IsClosed (Set.range (locus f).ι)
  rw [Scheme.Opens.range_ι]
  exact locus_closed f

instance inclusion_mono : Mono (inclusion f) := Over.mono_of_mono_left _

instance image_finite : IsFinite (image f).hom := by
  have : IsFinite (inclusion f).left := inferInstance
  exact inferInstanceAs (IsFinite ((inclusion f).left ≫ Y.hom))

instance image_etale : Etale (image f).hom :=
  inferInstanceAs (Etale ((inclusion f).left ≫ Y.hom))

noncomputable def factor : X ⟶ image f := by
  have hr : Set.range f.left ⊆ Set.range (locus f).ι := by
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.refl _
  let l := IsOpenImmersion.lift (locus f).ι f.left hr
  have hl : l ≫ (locus f).ι = f.left := IsOpenImmersion.lift_fac _ _ hr
  exact Over.homMk l (by
    change l ≫ ((locus f).ι ≫ Y.hom) = X.hom
    rw [← Category.assoc, hl, f.w])

@[simp, reassoc]
theorem factor_inclusion : factor f ≫ inclusion f = f := by
  apply Over.OverMorphism.ext
  change IsOpenImmersion.lift (locus f).ι f.left _ ≫ (locus f).ι = f.left
  exact IsOpenImmersion.lift_fac _ _ _

instance factor_surjective : Surjective (factor f).left := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := y.property
  refine ⟨x, ?_⟩
  apply (inclusion f).left.injective
  have he := congrArg (fun a : X ⟶ Y => a.left x) (factor_inclusion f)
  exact he.trans hx

instance factor_finite : IsFinite (factor f).left :=
  (FiniteEtaleLift.FiniteEtaleLimits.hom_finite_etale (factor f)).1

instance factor_etale : Etale (factor f).left :=
  (FiniteEtaleLift.FiniteEtaleLimits.hom_finite_etale (factor f)).2

theorem factors_iff_range {T : Over S} (a : T ⟶ Y) :
    (∃ b : T ⟶ image f, b ≫ inclusion f = a) ↔ Set.range a.left ⊆ Set.range f.left := by
  constructor
  · rintro ⟨b, rfl⟩ _ ⟨x, rfl⟩
    exact (b.left x).property
  · intro hr
    have hr' : Set.range a.left ⊆ Set.range (inclusion f).left := by
      change Set.range a.left ⊆ Set.range (locus f).ι
      rw [Scheme.Opens.range_ι]
      exact hr
    let l := IsOpenImmersion.lift (inclusion f).left a.left hr'
    have hl : l ≫ (inclusion f).left = a.left := IsOpenImmersion.lift_fac _ _ _
    have hb : l ≫ (image f).hom = T.hom := by
      rw [← (inclusion f).w, ← Category.assoc, hl, a.w]
    exact ⟨Over.homMk l hb, Over.OverMorphism.ext hl⟩

theorem geometric_factors_iff (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (a : Over.mk s ⟶ Y) :
    (∃ b : Over.mk s ⟶ image f, b ≫ inclusion f = a) ↔
      ∃ x : Over.mk s ⟶ X, x ≫ f = a := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨x, hx⟩ := IsogenyQuotient.Geometric.Points.Construction.surjective_on_geometric_points (factor f) K s b
    change x ≫ factor f = b at hx
    exact ⟨x, by rw [← factor_inclusion f, ← Category.assoc, hx, hb]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x ≫ factor f, by rw [Category.assoc, factor_inclusion]⟩

/-- Membership in the open scheme image can be tested on geometric points
of an arbitrary, possibly nonreduced, test scheme. -/
theorem factors_iff_geometric {T : Over S} (a : T ⟶ Y) :
    (∃ b : T ⟶ image f, b ≫ inclusion f = a) ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (s : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk s ⟶ T),
        ∃ b : Over.mk s ⟶ image f, b ≫ inclusion f = x ≫ a := by
  constructor
  · rintro ⟨b, hb⟩ K hK hclosed s x
    exact ⟨x ≫ b, by rw [Category.assoc, hb]⟩
  · intro h
    apply (factors_iff_range f a).mpr
    rintro _ ⟨x, rfl⟩
    let K := AlgebraicClosure (T.left.residueField x)
    let i := Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) K))
    let p := i ≫ T.left.fromSpecResidueField x
    let s := p ≫ T.hom
    let t : Over.mk s ⟶ T := Over.homMk p rfl
    obtain ⟨b, hb⟩ := h K s t
    have hr := (factors_iff_range f (t ≫ a)).mp ⟨b, hb⟩
    have he := hr ⟨(default : Spec (CommRingCat.of K)), rfl⟩
    change a.left (T.left.fromSpecResidueField x (i default)) ∈ Set.range f.left at he
    rwa [Scheme.fromSpecResidueField_apply] at he

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteEtaleIff.FiniteEtaleImage
