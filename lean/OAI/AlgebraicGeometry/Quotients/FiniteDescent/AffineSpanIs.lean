import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.EquivalenceRelation

/-! # Affine Span Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSpanIs.Construction.AffineSpan

/-!
# The spanning condition for a closed affine relation

For a closed relation in an affine fiber product, the target-valued functions
span the relation ring as a module over the source ring.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- A finite-source equivalence relation on a separated scheme has a closed
relation morphism into the relative square. -/
theorem relation_isClosedImmersion
    {U V S : Scheme.{u}} (a : U ⟶ S) [IsSeparated a]
    (s t : V ⟶ U) [IsFinite s] [JointlyMono₂ s t] (h : s ≫ a = t ≫ a) :
    IsClosedImmersion (pullback.lift s t h) := by
  let i := pullback.lift s t h
  have : Mono i := by
    constructor
    intro T f g hfg
    apply JointlyMono₂.right_cancellation (p₁ := s) (p₂ := t) f g
    · simpa only [i, Category.assoc, pullback.lift_fst] using
        congrArg (fun k => k ≫ pullback.fst a a) hfg
    · simpa only [i, Category.assoc, pullback.lift_snd] using
        congrArg (fun k => k ≫ pullback.snd a a) hfg
  have : IsFinite (i ≫ pullback.fst a a) := by
    change IsFinite (pullback.lift s t h ≫ pullback.fst a a)
    rw [pullback.lift_fst]
    infer_instance
  have : IsFinite i := IsFinite.of_comp i (pullback.fst a a)
  exact (IsClosedImmersion.iff_isFinite_and_mono i).mpr ⟨inferInstance, inferInstance⟩

/-- A surjective image of a ring pushout is spanned over the first ring by
the image of the second ring. -/
theorem span_of_isPushout_of_surjective
    {R A₁ A₂ P B : CommRingCat.{u}}
    (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂) (p₁ : A₁ ⟶ P) (p₂ : A₂ ⟶ P)
    (h : IsPushout a₁ a₂ p₁ p₂) (f : P ⟶ B) (hf : Function.Surjective f) :
    letI := (f.hom.comp p₁.hom).toAlgebra
    Submodule.span A₁ (Set.range (f.hom.comp p₂.hom)) = ⊤ := by
  let := a₁.hom.toAlgebra
  let := a₂.hom.toAlgebra
  let := p₁.hom.toAlgebra
  let := p₂.hom.toAlgebra
  let := (p₁.hom.comp a₁.hom).toAlgebra
  let := (f.hom.comp p₁.hom).toAlgebra
  have : IsScalarTower R A₁ P := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R A₂ P := IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (fun k : R ⟶ P => k r) h.w
  have hpush : Algebra.IsPushout R A₁ A₂ P := CommRingCat.isPushout_iff_isPushout.mp h
  apply top_le_iff.mp
  intro b _
  obtain ⟨x, rfl⟩ := hf b
  refine hpush.out.inductionOn x ?_ ?_ ?_
  · intro a
    exact Submodule.subset_span ⟨a, rfl⟩
  · intro a x hx
    change f (p₁ a * x) ∈ _
    rw [map_mul]
    exact Submodule.smul_mem _ a hx
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- A closed relation in an affine fiber product has the required module
spanning property on coordinate rings. -/
theorem span_of_closedImmersion
    {U V S : Scheme.{u}} [IsAffine U] [IsAffine S]
    (a : U ⟶ S) (s t : V ⟶ U) (h : s ≫ a = t ≫ a)
    [IsClosedImmersion (pullback.lift s t h)] :
    letI := s.appTop.hom.toAlgebra
    Submodule.span Γ(U, ⊤) (Set.range t.appTop.hom) = ⊤ := by
  let i := pullback.lift s t h
  have hsurj : Function.Surjective i.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hpush := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback a a)
  have hspan := span_of_isPushout_of_surjective a.appTop a.appTop
    (pullback.fst a a).appTop (pullback.snd a a).appTop hpush i.appTop hsurj
  have hs : i.appTop.hom.comp (pullback.fst a a).appTop.hom = s.appTop.hom := by
    ext x
    change (pullback.lift s t h).appTop ((pullback.fst a a).appTop x) = s.appTop x
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      congrArg (fun f : V ⟶ U => f.appTop x) (pullback.lift_fst s t h)
  have ht : i.appTop.hom.comp (pullback.snd a a).appTop.hom = t.appTop.hom := by
    ext x
    change (pullback.lift s t h).appTop ((pullback.snd a a).appTop x) = t.appTop x
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      congrArg (fun f : V ⟶ U => f.appTop x) (pullback.lift_snd s t h)
  rw [hs, ht] at hspan
  exact hspan

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSpanIs.Construction.AffineSpan
