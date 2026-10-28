import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.HomParametersMul
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleEqualityIs

/-! # Embedding Parameters Is -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters

/-!
# TorsionQuotient: the clopen parameter locus of injective group markings

Distinct labels must remain distinct on every field-valued test point.
This condition cuts out the complement of finitely many clopen collision
loci inside the actual homomorphism parameter scheme.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (H : Over S) [GrpObj H]
variable (M : Type u) [Group M] [Fintype M]

def Distinct {T : Over S} (a : M →* (T ⟶ H)) : Prop :=
  ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (t : Over.mk s ⟶ T),
    Function.Injective (fun m => t ≫ a m)

abbrev Choice (T : Over S) := {a : M →* (T ⟶ H) // Distinct H M a}

abbrev DifferentPairs := {p : M × M // p.1 ≠ p.2}

noncomputable def collision (a b : M) : Set (HomParametersMul.HomParameters.parameter H M).left :=
  Set.range (equalizer.ι (HomParametersMul.HomParameters.coefficient H M a) (HomParametersMul.HomParameters.coefficient H M b)).left

noncomputable def embeddingSet : Set (HomParametersMul.HomParameters.parameter H M).left :=
  ⋂ p : DifferentPairs M, (collision H M p.val.1 p.val.2)ᶜ

variable [IsFinite H.hom] [Etale H.hom]

theorem embeddingSet_isClopen : IsClopen (embeddingSet H M) :=
  isClopen_iInter_of_finite fun p =>
    (EtaleEqualityIs.EtaleEquality.range_isClopen (HomParametersMul.HomParameters.coefficient H M p.val.1)
      (HomParametersMul.HomParameters.coefficient H M p.val.2)).compl

noncomputable def locus : (HomParametersMul.HomParameters.parameter H M).left.Opens :=
  ⟨embeddingSet H M, (embeddingSet_isClopen H M).isOpen⟩

noncomputable def parameter : Over S :=
  Over.mk ((locus H M).ι ≫ (HomParametersMul.HomParameters.parameter H M).hom)

noncomputable def inclusion : parameter H M ⟶ HomParametersMul.HomParameters.parameter H M :=
  Over.homMk (locus H M).ι rfl

instance inclusion_mono : Mono (inclusion H M) := by
  let : Mono (inclusion H M).left := inferInstanceAs (Mono (locus H M).ι)
  exact Over.mono_of_mono_left _

theorem finite_etale : IsFinite (parameter H M).hom ∧ Etale (parameter H M).hom := by
  have hc : IsClosed (Set.range (locus H M).ι) := by
    rw [Scheme.Opens.range_ι]
    exact (embeddingSet_isClopen H M).isClosed
  let : IsClosedImmersion (locus H M).ι := IsClosedImmersion.of_isPreimmersion _ hc
  change IsFinite ((locus H M).ι ≫ (HomParametersMul.HomParameters.parameter H M).hom) ∧
    Etale ((locus H M).ι ≫ (HomParametersMul.HomParameters.parameter H M).hom)
  exact ⟨inferInstance, inferInstance⟩

theorem range_iff_distinct {T : Over S} (a : T ⟶ HomParametersMul.HomParameters.parameter H M) :
    Set.range a.left ⊆ embeddingSet H M ↔ Distinct H M (HomParametersMul.HomParameters.points H M T a) := by
  constructor
  · intro hr K hK s t x y hxy
    by_contra hne
    have he : (t ≫ a) ≫ HomParametersMul.HomParameters.coefficient H M x =
        (t ≫ a) ≫ HomParametersMul.HomParameters.coefficient H M y := by
      exact (Category.assoc _ _ _).trans (hxy.trans (Category.assoc _ _ _).symm)
    have hc := (EtaleEqualityIs.EtaleEquality.equalizes_iff_range_subset
      (HomParametersMul.HomParameters.coefficient H M x) (HomParametersMul.HomParameters.coefficient H M y) (t ≫ a)).mp he
    let z : Spec (CommRingCat.of K) := default
    have hg := Set.mem_iInter.mp (hr ⟨t.left z, rfl⟩) ⟨(x, y), hne⟩
    exact hg (hc ⟨z, rfl⟩)
  · intro hd
    rintro _ ⟨x, rfl⟩
    apply Set.mem_iInter.mpr
    intro p hp
    let K := T.left.residueField x
    let s := T.left.fromSpecResidueField x ≫ T.hom
    let t : Over.mk s ⟶ T := Over.homMk (T.left.fromSpecResidueField x) rfl
    have hr : Set.range (t ≫ a).left ⊆ collision H M p.val.1 p.val.2 := by
      rintro _ ⟨z, rfl⟩
      change a.left (T.left.fromSpecResidueField x z) ∈ collision H M p.val.1 p.val.2
      rw [Scheme.fromSpecResidueField_apply]
      exact hp
    have he := (EtaleEqualityIs.EtaleEquality.equalizes_iff_range_subset
      (HomParametersMul.HomParameters.coefficient H M p.val.1) (HomParametersMul.HomParameters.coefficient H M p.val.2) (t ≫ a)).mpr hr
    apply p.property
    apply hd K s t
    exact (Category.assoc _ _ _).symm.trans (he.trans (Category.assoc _ _ _))

noncomputable def points (T : Over S) (a : T ⟶ parameter H M) : Choice H M T :=
  ⟨HomParametersMul.HomParameters.points H M T (a ≫ inclusion H M),
    (range_iff_distinct H M (a ≫ inclusion H M)).mp (by
      rintro _ ⟨x, rfl⟩
      exact (a.left x).property)⟩

theorem points_injective (T : Over S) : Function.Injective (points H M T) := by
  intro a b hab
  apply (cancel_mono (inclusion H M)).mp
  apply (HomParametersMul.HomParameters.pointsEquiv H M T).injective
  exact congrArg Subtype.val hab

theorem points_surjective (T : Over S) : Function.Surjective (points H M T) := by
  intro c
  let f := HomParametersMul.HomParameters.fromPoints H M c.val
  have hf : HomParametersMul.HomParameters.points H M T f = c.val :=
    (HomParametersMul.HomParameters.pointsEquiv H M T).apply_symm_apply c.val
  have hr : Set.range f.left ⊆ embeddingSet H M :=
    (range_iff_distinct H M f).mpr (hf.symm ▸ c.property)
  have hr' : Set.range f.left ⊆ Set.range (locus H M).ι := by
    rw [Scheme.Opens.range_ι]
    exact hr
  let l := IsOpenImmersion.lift (locus H M).ι f.left hr'
  have hl : l ≫ (locus H M).ι = f.left := IsOpenImmersion.lift_fac _ _ hr'
  have hbase : l ≫ (parameter H M).hom = T.hom := by
    change l ≫ ((locus H M).ι ≫ (HomParametersMul.HomParameters.parameter H M).hom) = T.hom
    rw [← Category.assoc, hl]
    exact Over.w f
  let a : T ⟶ parameter H M := Over.homMk l hbase
  have ha : a ≫ inclusion H M = f := Over.OverMorphism.ext hl
  refine ⟨a, ?_⟩
  apply Subtype.ext
  change HomParametersMul.HomParameters.points H M T (a ≫ inclusion H M) = c.val
  rw [ha]
  exact hf

noncomputable def pointsEquiv (T : Over S) : (T ⟶ parameter H M) ≃ Choice H M T :=
  Equiv.ofBijective (points H M T) ⟨points_injective H M T, points_surjective H M T⟩

noncomputable def baseChange {T U : Over S} (a : Choice H M T) (f : U ⟶ T) : Choice H M U :=
  ⟨{ toFun := fun m => f ≫ a.val m
     map_one' := by rw [a.val.map_one, MonObj.comp_one]
     map_mul' x y := by rw [a.val.map_mul, MonObj.comp_mul] }, by
    intro K hK s t x y hxy
    apply a.property K s (t ≫ f)
    exact (Category.assoc _ _ _).trans (hxy.trans (Category.assoc _ _ _).symm)⟩

noncomputable def pointFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Choice H M T.unop
  map f := ↾fun a => baseChange H M a f.unop
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    apply MonoidHom.ext
    intro m
    change (𝟙 T.unop) ≫ a.val m = a.val m
    exact Category.id_comp _
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    apply MonoidHom.ext
    intro m
    change (g.unop ≫ f.unop) ≫ a.val m = g.unop ≫ f.unop ≫ a.val m
    exact Category.assoc _ _ _

noncomputable def representable : (pointFunctor H M).RepresentableBy (parameter H M) where
  homEquiv := pointsEquiv H M _
  homEquiv_comp f a := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro m
    change ((f ≫ a) ≫ inclusion H M) ≫ HomParametersMul.HomParameters.coefficient H M m =
      f ≫ ((a ≫ inclusion H M) ≫ HomParametersMul.HomParameters.coefficient H M m)
    simp only [Category.assoc]

instance parameter_isFinite : IsFinite (parameter H M).hom := (finite_etale H M).1

instance parameter_etale : Etale (parameter H M).hom := (finite_etale H M).2

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters
