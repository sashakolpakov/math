import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Limits
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRing
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupoidIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineGroupoidIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineQuotientOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantOpensEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SourceTrivializationTop
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelationRestrictionOn
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.QuotientGluingIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCoverExistsQuotient
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Group
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Proper
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupSmoothOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantAffineHas
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrbitQuotientExists
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Affine
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupIrreducibleOf
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Epi -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Epi.Construction

/-!
# FiniteDescent: quotient descent

The complete quotient theorem is proved in `Proofs/FiniteDescentFinal.lean`.
`Proofs/StatementCheck.lean` checks the exact declarations and theorem
signature from the unchanged `Statements/FiniteDescent.lean`.

This module supplies quotient descent, the exact translation kernel, and the
universal property for invariant morphisms. The supporting modules construct
finite locally free affine quotients and glue their charts, descend the group
structure and abelian-scheme properties, and prove the required invariant
affine neighborhoods. The remaining multiplication-finiteness input is supplied
by the geometric cube identity in `Proofs/GeometricCubeIdentity.lean`, using
projective modifications, product seesaw, and faithful Picard descent.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u v

section Descent

variable {C : Type u} [Category.{v} C] {S : C}

/-- Descent along an effective epimorphism also respects a fixed base. -/
theorem existsUnique_desc_over
    {A B T : Over S} (q : A ⟶ B) [EffectiveEpi q.left]
    (f : A ⟶ T)
    (hf : ∀ (U : Over S) (a b : U ⟶ A),
      a ≫ q = b ≫ q → a ≫ f = b ≫ f) :
    ∃! g : B ⟶ T, q ≫ g = f := by
  have hleft : ∀ {Z : C} (a b : Z ⟶ A.left),
      a ≫ q.left = b ≫ q.left → a ≫ f.left = b ≫ f.left := by
    intro Z a b hab
    have hb : b ≫ A.hom = a ≫ A.hom := by
      rw [← q.w, ← Category.assoc, ← Category.assoc, hab]
    let a' : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk a rfl
    let b' : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk b hb
    have hab' : a' ≫ q = b' ≫ q := Over.OverMorphism.ext hab
    exact congrArg (fun e => e.left) (hf _ a' b' hab')
  let g := EffectiveEpi.desc q.left f.left hleft
  have hg : q.left ≫ g = f.left := EffectiveEpi.fac _ _ _
  have hbase : g ≫ T.hom = B.hom := by
    apply (cancel_epi q.left).mp
    rw [← Category.assoc, hg, f.w, q.w]
  refine ⟨Over.homMk g hbase, Over.OverMorphism.ext hg, ?_⟩
  intro g' hg'
  apply Over.OverMorphism.ext
  exact EffectiveEpi.uniq q.left f.left hleft g'.left
    (congrArg (fun e => e.left) hg')

/-- An effective epimorphism of underlying objects remains effective in the
category of objects over a fixed base. -/
theorem effectiveEpi_over_of_left {A B : Over S} (q : A ⟶ B) [EffectiveEpi q.left] :
    EffectiveEpi q := by
  classical
  refine ⟨⟨{
    desc := fun f hf => (existsUnique_desc_over q f (fun _ a b => hf a b)).choose
    fac := fun f hf => (existsUnique_desc_over q f (fun _ a b => hf a b)).choose_spec.1
    uniq := fun f hf g hg =>
      (existsUnique_desc_over q f (fun _ a b => hf a b)).choose_spec.2 g hg
  }⟩⟩

end Descent

section Groups

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {A B H : C} [GrpObj A] [GrpObj B]
variable (i : H ⟶ A) [Mono i]
variable (q : A ⟶ B) [IsMonHom q]

omit [GrpObj A] [IsMonHom q] in
/-- The all-test-object kernel condition implies that every subgroup-valued
point maps to the identity. -/
theorem subgroup_point_comp_eq_one
    (hker : ∀ (T : C) (a : T ⟶ A),
      a ≫ q = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a)
    (T : C) (h : T ⟶ H) :
    (h ≫ i) ≫ q = 1 := by
  apply (hker T (h ≫ i)).mpr
  exact ⟨h, rfl, fun h' hh' => (cancel_mono i).mp hh'⟩

/-- Fibers of a group homomorphism with the specified kernel are exactly
the free translation orbits of that kernel, on every test object. -/
theorem same_image_iff_unique_translate
    (hker : ∀ (T : C) (a : T ⟶ A),
      a ≫ q = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a)
    (T : C) (a b : T ⟶ A) :
    a ≫ q = b ≫ q ↔ ∃! h : T ⟶ H, (h ≫ i) * b = a := by
  constructor
  · intro hab
    have hk : (a * b⁻¹) ≫ q = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hab, mul_inv_cancel]
    obtain ⟨h, hh, hu⟩ := (hker T (a * b⁻¹)).mp hk
    refine ⟨h, ?_, ?_⟩
    · change (h ≫ i) * b = a
      rw [hh]
      exact inv_mul_cancel_right a b
    · intro h' hh'
      apply hu
      exact (eq_mul_inv_iff_mul_eq).mpr hh'
  · rintro ⟨h, hh, _⟩
    rw [← hh, MonObj.mul_comp, subgroup_point_comp_eq_one i q hker, one_mul]

/-- An invariant morphism equalizes the entire kernel relation. -/
theorem invariant_equalizes_kernel
    (hker : ∀ (T : C) (a : T ⟶ A),
      a ≫ q = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a)
    {T : C} (f : A ⟶ T)
    (hf : ∀ (U : C) (a : U ⟶ A) (h : U ⟶ H),
      ((h ≫ i) * a) ≫ f = a ≫ f)
    (U : C) (a b : U ⟶ A) (hab : a ≫ q = b ≫ q) :
    a ≫ f = b ≫ f := by
  obtain ⟨h, hh, _⟩ := (same_image_iff_unique_translate i q hker U a b).mp hab
  rw [← hh]
  exact hf U b h

end Groups

section Translations

open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {A H : C} [GrpObj A]

/-- The subgroup translation action `(h, a) ↦ i(h) * a`. -/
abbrev translation (i : H ⟶ A) : H ⊗ A ⟶ A :=
  (fst H A ≫ i) * snd H A

/-- Translation is a projection after an isomorphism of the product. -/
noncomputable def translationShear (i : H ⟶ A) : H ⊗ A ≅ H ⊗ A where
  hom := lift (fst H A) (translation i)
  inv := lift (fst H A) ((fst H A ≫ i)⁻¹ * snd H A)
  hom_inv_id := by
    apply hom_ext
    · simp
    · simp [translation, MonObj.comp_mul, GrpObj.comp_inv]
  inv_hom_id := by
    apply hom_ext
    · simp
    · simp [translation, MonObj.comp_mul]

@[simp]
theorem translationShear_hom_snd (i : H ⟶ A) :
    (translationShear i).hom ≫ snd H A = translation i := by
  exact lift_snd _ _

/-- The coordinate change `(x, a) ↦ (x * a, a)`. -/
noncomputable def translationCoordinates (A : C) [GrpObj A] : A ⊗ A ≅ A ⊗ A where
  hom := lift (fst A A * snd A A) (snd A A)
  inv := lift (fst A A * (snd A A)⁻¹) (snd A A)
  hom_inv_id := by
    apply hom_ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv]
    · simp
  inv_hom_id := by
    apply hom_ext
    · simp [MonObj.comp_mul]
    · simp

/-- The action relation is the product of the subgroup immersion with the
identity, followed by a coordinate isomorphism. -/
theorem translation_relation_factorization (i : H ⟶ A) :
    lift (translation i) (snd H A) =
      (i ⊗ₘ 𝟙 A) ≫ (translationCoordinates A).hom := by
  apply hom_ext <;> simp [translationCoordinates, translation, MonObj.comp_mul]

/-- A subgroup acts freely: a pair of source and target maps determines
the translating subgroup element uniquely. -/
theorem translation_jointlyMono (i : H ⟶ A) [Mono i] :
    JointlyMono₂ (snd H A) (translation i) := by
  constructor
  intro T f g hs ht
  apply hom_ext
  · apply (cancel_mono i).mp
    have heq : (f ≫ fst H A ≫ i) * (f ≫ snd H A) =
        (g ≫ fst H A ≫ i) * (g ≫ snd H A) := by
      simpa [translation, MonObj.comp_mul] using ht
    rw [hs] at heq
    simpa only [Category.assoc] using mul_right_cancel heq
  · exact hs

/-- The translation relation is an internal equivalence relation. -/
noncomputable def translationEquivalenceRelation
    [Limits.HasPullbacks C] [GrpObj H]
    (i : H ⟶ A) [IsMonHom i] [Mono i] :
    CategoryTheory.EquivalenceRelation (snd H A) (translation i) where
  toJointlyMono₂ := translation_jointlyMono i
  r := lift 1 (𝟙 A)
  reflexivity₁ := by simp
  reflexivity₂ := by simp [translation, MonObj.comp_mul, MonObj.one_comp]
  s := lift (fst H A)⁻¹ (translation i)
  symmetry₁ := by simp
  symmetry₂ := by simp [translation, MonObj.comp_mul, GrpObj.inv_comp]
  c := Limits.pullback.cone (translation i) (snd H A)
  isLimit := Limits.pullback.isLimit _ _
  t := lift
    ((Limits.pullback.snd (translation i) (snd H A) ≫ fst H A) *
      (Limits.pullback.fst (translation i) (snd H A) ≫ fst H A))
    (Limits.pullback.fst (translation i) (snd H A) ≫ snd H A)
  transitivity₁ := by simp
  transitivity₂ := by
    change
      lift
        ((Limits.pullback.snd (translation i) (snd H A) ≫ fst H A) *
          (Limits.pullback.fst (translation i) (snd H A) ≫ fst H A))
        (Limits.pullback.fst (translation i) (snd H A) ≫ snd H A) ≫
        translation i = Limits.pullback.snd (translation i) (snd H A) ≫ translation i
    have hp := Limits.pullback.condition (f := translation i) (g := snd H A)
    simp only [translation, MonObj.comp_mul] at hp ⊢
    simp only [lift_fst_assoc, lift_snd, MonObj.mul_comp, Category.assoc]
    rw [mul_assoc, hp]

end Translations

section FiniteRelation

open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme.{u}} {A H : Over S} [GrpObj A]

/-- Finite locally freeness of the subgroup makes the action map finite
locally free, by the translation shear isomorphism. -/
theorem translation_finite_flat_finitelyPresented
    (i : H ⟶ A) [IsFinite H.hom] [Flat H.hom]
    [LocallyOfFinitePresentation H.hom] :
    IsFinite (translation i).left ∧ Flat (translation i).left ∧
      LocallyOfFinitePresentation (translation i).left := by
  rw [← translationShear_hom_snd i]
  change
    IsFinite ((translationShear i).hom.left ≫ (snd H A).left) ∧
      Flat ((translationShear i).hom.left ≫ (snd H A).left) ∧
      LocallyOfFinitePresentation ((translationShear i).hom.left ≫ (snd H A).left)
  have : IsFinite (snd H A).left := inferInstanceAs
    (IsFinite (Limits.pullback.snd H.hom A.hom))
  have : Flat (snd H A).left := inferInstanceAs
    (Flat (Limits.pullback.snd H.hom A.hom))
  have : LocallyOfFinitePresentation (snd H A).left := inferInstanceAs
    (LocallyOfFinitePresentation (Limits.pullback.snd H.hom A.hom))
  have : IsIso (translationShear i).hom.left := inferInstanceAs
    (IsIso ((Over.forget S).map (translationShear i).hom))
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- A closed subgroup gives a closed translation equivalence relation. -/
theorem translation_relation_closedImmersion
    (i : H ⟶ A) [IsClosedImmersion i.left] :
    IsClosedImmersion (lift (translation i) (snd H A)).left := by
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    ⟨fun _ _ hf hg => by
      let := hf
      let := hg
      infer_instance⟩
  have hi : IsClosedImmersion (i ⊗ₘ 𝟙 A).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (inferInstance : IsClosedImmersion i.left)
      (inferInstance : IsClosedImmersion (𝟙 A.left)) i.w.symm (by simp)
  have he : IsIso (translationCoordinates A).hom.left := inferInstanceAs
    (IsIso ((Over.forget S).map (translationCoordinates A).hom))
  rw [translation_relation_factorization]
  change IsClosedImmersion ((i ⊗ₘ 𝟙 A).left ≫ (translationCoordinates A).hom.left)
  infer_instance

/-- The structure map of a group scheme is surjective, by its identity section. -/
theorem group_structureMap_surjective (G : Over S) [GrpObj G] :
    Surjective G.hom := by
  constructor
  intro s
  refine ⟨η[G].left s, ?_⟩
  change (η[G].left ≫ G.hom) s = s
  rw [η[G].w]
  rfl

/-- Both projections of the subgroup translation relation are surjective. -/
theorem translation_relation_surjective [GrpObj H] (i : H ⟶ A) :
    Surjective (snd H A).left ∧ Surjective (translation i).left := by
  have : Surjective H.hom := group_structureMap_surjective H
  have hs : Surjective (snd H A).left := inferInstanceAs
    (Surjective (Limits.pullback.snd H.hom A.hom))
  refine ⟨hs, ?_⟩
  rw [← translationShear_hom_snd i]
  have : IsIso (translationShear i).hom.left := inferInstanceAs
    (IsIso ((Over.forget S).map (translationShear i).hom))
  change Surjective ((translationShear i).hom.left ≫ (snd H A).left)
  infer_instance

end FiniteRelation

section SchemeGroupDescent

open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme.{u}}

/-- Products of finite flat surjections over the base are again finite flat
surjections. This supplies the epimorphisms used to descend the group laws. -/
theorem tensor_finite_flat_surjective {A B A' B' : Over S}
    (q : A ⟶ B) (r : A' ⟶ B')
    [IsFinite q.left] [Flat q.left] [Surjective q.left]
    [IsFinite r.left] [Flat r.left] [Surjective r.left] :
    IsFinite (q ⊗ₘ r).left ∧ Flat (q ⊗ₘ r).left ∧ Surjective (q ⊗ₘ r).left := by
  have : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    ⟨fun _ _ hf hg => by
      let := hf
      let := hg
      infer_instance⟩
  rw [Over.tensorHom_left]
  exact ⟨MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance
      q.w.symm r.w.symm,
    MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance q.w.symm r.w.symm,
    MorphismProperty.pullbackMap (P := @Surjective) inferInstance inferInstance q.w.symm r.w.symm⟩

/-- A finite flat surjective scheme quotient with the exact translation
relation inherits the commutative group structure and the prescribed
scheme-theoretic subgroup kernel. -/
theorem commutativeGroup_of_translation_kernelPair
    {A B H : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj H]
    (i : H ⟶ A) [Mono i] [IsMonHom i] (q : A ⟶ B)
    [IsFinite q.left] [Flat q.left] [Surjective q.left]
    (hk : IsKernelPair q.left (snd H A).left (translation i).left) :
    ∃ g : GrpObj B, letI := g
      IsCommMonObj B ∧ IsMonHom q ∧
      ∀ (T : Over S) (a : T ⟶ A), a ≫ q = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a := by
  have hk' : IsKernelPair q (snd H A) (translation i) :=
    IsPullback.of_map_of_faithful (Over.forget S) hk
  have : EffectiveEpi q := effectiveEpi_over_of_left q
  obtain ⟨h₂fin, h₂flat, h₂surj⟩ := tensor_finite_flat_surjective q q
  let := h₂fin
  let := h₂flat
  let := h₂surj
  have : EffectiveEpi (q ⊗ₘ q) := effectiveEpi_over_of_left (q ⊗ₘ q)
  obtain ⟨h₃fin, h₃flat, h₃surj⟩ := tensor_finite_flat_surjective (q ⊗ₘ q) q
  let := h₃fin
  let := h₃flat
  let := h₃surj
  have : EffectiveEpi ((q ⊗ₘ q) ⊗ₘ q) := effectiveEpi_over_of_left ((q ⊗ₘ q) ⊗ₘ q)
  let g := Group.Construction.GroupDescent.group i q hk'
  let := g
  have hcomm : IsCommMonObj B := Group.Construction.GroupDescent.isCommMonObj_group i q hk'
  have hmon : IsMonHom q := Group.Construction.GroupDescent.isMonHom_group i q hk'
  refine ⟨g, hcomm, hmon, ?_⟩
  intro T a
  simpa only [MonObj.one_comp] using Group.Construction.GroupDescent.kernel i q hk' T a

/-- Once the finite locally free scheme quotient and its group structure have
been constructed, all geometric properties in the abelian-scheme bundle
descend from the source. -/
theorem quotient_geometric_properties
    {A B : Over S} [GrpObj A] [GrpObj B]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (q : A ⟶ B) [IsMonHom q]
    [IsFinite q.left] [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    IsProper B.hom ∧ Smooth B.hom ∧ GeometricallyConnected B.hom := by
  have : GeometricallyConnected (q.left ≫ B.hom) := by rw [q.w]; infer_instance
  exact ⟨GroupOf.Construction.GroupGeometry.proper_of_finite_quotient q, GroupSmoothOf.Construction.GroupSmooth.smooth_of_finite_quotient q,
    Proper.Construction.Geometry.geometricallyConnected_of_comp q.left B.hom⟩

end SchemeGroupDescent

section SheafQuotient

open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Limits

/-- The functor of points on the relative fppf site. The codomain universe
is enlarged so that the general sheafification construction applies. -/
noncomputable abbrev relativeYoneda (S : Scheme.{u}) :
    Over S ⥤ Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}

variable {S : Scheme.{u}} {A H : Over S} [GrpObj A]

/-- The fppf quotient exists as a sheaf by taking the coequalizer of the
action and projection. This definition asserts no scheme representability. -/
noncomputable def quotientSheaf (i : H ⟶ A) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  coequalizer ((relativeYoneda S).map (translation i))
    ((relativeYoneda S).map (snd H A))

/-- The canonical morphism to the actual quotient sheaf. -/
noncomputable def quotientSheafProjection (i : H ⟶ A) :
    (relativeYoneda S).obj A ⟶ quotientSheaf i :=
  coequalizer.π _ _

/-- The action and projection have equal composites with the quotient map. -/
theorem quotientSheaf_condition (i : H ⟶ A) :
    (relativeYoneda S).map (translation i) ≫ quotientSheafProjection i =
      (relativeYoneda S).map (snd H A) ≫ quotientSheafProjection i := by
  exact coequalizer.condition _ _

/-- The constructed fppf sheaf has the quotient universal property. -/
theorem quotientSheaf_universal_property
    (i : H ⟶ A) (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    (f : (relativeYoneda S).obj A ⟶ F)
    (hf : (relativeYoneda S).map (translation i) ≫ f =
      (relativeYoneda S).map (snd H A) ≫ f) :
    ∃! g : quotientSheaf i ⟶ F, quotientSheafProjection i ≫ g = f := by
  refine ⟨coequalizer.desc f hf, coequalizer.π_desc f hf, ?_⟩
  intro g hg
  apply coequalizer.hom_ext
  exact hg.trans (coequalizer.π_desc f hf).symm

end SheafQuotient

/-- The universal property required by FiniteDescent follows from fpqc descent once
the scheme quotient and its scheme-theoretic kernel have been constructed. -/
theorem quotient_universal_property
    {S : Scheme.{u}} {A B H : Over S}
    [GrpObj A] [GrpObj B] [GrpObj H]
    (i : H ⟶ A) [IsMonHom i] [IsClosedImmersion i.left]
    (q : A ⟶ B) [IsMonHom q]
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A),
      a ≫ q = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a)
    (T : Over S) (f : A ⟶ T)
    (hf : ∀ (U : Over S) (a : U ⟶ A) (h : U ⟶ H),
      ((h ≫ i) * a) ≫ f = a ≫ f) :
    ∃! g : B ⟶ T, q ≫ g = f := by
  have : Mono i := Over.mono_of_mono_left i
  exact existsUnique_desc_over q f (invariant_equalizes_kernel i q hker f hf)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Epi.Construction
