import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction

/-! # Surjective Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SurjectiveLocus

noncomputable section

/-!
An actual closed parameter space for surjectivity of a proper map into an
open family. This is used to impose generation in an arithmetic parameter
space. Both the scheme and its reduced-test-scheme classifying property
are constructed; neither is a parameter-space assumption.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {B : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)

def surjectiveParameterSet : Set B :=
  (Y.hom '' (Set.range f.left)ᶜ)ᶜ

theorem mem_surjectiveParameterSet (b : B) :
    b ∈ surjectiveParameterSet f ↔
      ∀ y : Y.left, Y.hom y = b → y ∈ Set.range f.left := by
  classical
  constructor
  · intro hb y hy
    by_contra h
    exact hb ⟨y, h, hy⟩
  · rintro hb ⟨y, hy, heq⟩
    exact hy (hb y heq)

/-- This condition is detected by the image of an arbitrary scheme base
change, including extension of its residue fields. -/
theorem surjective_base_change_iff_range {S : Scheme.{u}} (g : S ⟶ B) :
    Surjective ((Over.pullback g).map f).left ↔
      Set.range g ⊆ surjectiveParameterSet f := by
  constructor
  · intro hs b hb
    obtain ⟨s, rfl⟩ := hb
    apply (mem_surjectiveParameterSet f (g s)).mpr
    intro y hy
    obtain ⟨yS, hyS, _⟩ := Scheme.Pullback.exists_preimage_pullback y s hy
    obtain ⟨xS, hxS⟩ := hs.surj yS
    refine ⟨pullback.fst X.hom g xS, ?_⟩
    have hcomp := (Specialization.base_change_square g f).w
    have heq := congrArg (fun m : pullback X.hom g ⟶ Y.left ↦ m xS) hcomp
    change f.left (pullback.fst X.hom g xS) = pullback.fst Y.hom g
      (((Over.pullback g).map f).left xS) at heq
    exact heq.trans ((congrArg (pullback.fst Y.hom g) hxS).trans hyS)
  · intro hg
    constructor
    intro yS
    let y := pullback.fst Y.hom g yS
    have hy : Y.hom y ∈ Set.range g := by
      refine ⟨pullback.snd Y.hom g yS, ?_⟩
      exact (congrArg (fun m : pullback Y.hom g ⟶ B ↦ m yS)
        (pullback.condition (f := Y.hom) (g := g))).symm
    obtain ⟨x, hx⟩ := (mem_surjectiveParameterSet f (Y.hom y)).mp (hg hy) y rfl
    obtain ⟨xS, _, hxS⟩ := Scheme.exists_preimage_of_isPullback
      (Specialization.base_change_square g f) x yS hx
    exact ⟨xS, hxS⟩

variable [IsProper f.left] [UniversallyOpen Y.hom]

theorem surjectiveParameterSet_closed : IsClosed (surjectiveParameterSet f) := by
  exact (Y.hom.isOpenMap _ f.left.isClosedMap.isClosed_range.isOpen_compl).isClosed_compl

def surjectiveParameterClosed : TopologicalSpace.Closeds B :=
  ⟨surjectiveParameterSet f, surjectiveParameterSet_closed f⟩

/-- The reduced induced closed subscheme on the surjectivity locus. -/
def surjectiveParameterScheme : Over B :=
  Reduction.reduction (Over.mk (Scheme.IdealSheafData.vanishingIdeal
    (surjectiveParameterClosed f)).subschemeι)

instance surjectiveParameterScheme_reduced : IsReduced (surjectiveParameterScheme f).left :=
  inferInstanceAs (IsReduced (Reduction.reduction _).left)

instance surjectiveParameterScheme_closed : IsClosedImmersion (surjectiveParameterScheme f).hom :=
  inferInstanceAs (IsClosedImmersion ((_ : Scheme.IdealSheafData _).subschemeι ≫
    (_ : Scheme.IdealSheafData _).subschemeι))

theorem surjectiveParameterScheme_range :
    Set.range (surjectiveParameterScheme f).hom = surjectiveParameterSet f := by
  let Z := Over.mk (Scheme.IdealSheafData.vanishingIdeal (surjectiveParameterClosed f)).subschemeι
  change Set.range ((Reduction.reductionι Z).left ≫ Z.hom) = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Reduction.reduction_range,
    Set.image_univ]
  change Set.range (Scheme.IdealSheafData.vanishingIdeal
    (surjectiveParameterClosed f)).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- The universal proper map over the constructed parameter scheme is
surjective. -/
theorem surjective_over_parameterScheme :
    Surjective ((Over.pullback (surjectiveParameterScheme f).hom).map f).left :=
  (surjective_base_change_iff_range f _).mpr (surjectiveParameterScheme_range f ▸ Set.Subset.rfl)

/-- The constructed closed scheme represents the surjectivity condition
on every reduced test scheme. -/
theorem surjective_parameterScheme_classifies {S : Scheme.{u}} [IsReduced S]
    (g : S ⟶ B) :
    Surjective ((Over.pullback g).map f).left ↔
      ∃! q : S ⟶ (surjectiveParameterScheme f).left,
        q ≫ (surjectiveParameterScheme f).hom = g := by
  rw [surjective_base_change_iff_range]
  constructor
  · intro hg
    have h : Set.range g ⊆ Set.range (surjectiveParameterScheme f).hom := by
      rw [surjectiveParameterScheme_range]
      exact hg
    let q := Albanese.Construction.ReducedFactor.factorThroughClosed (surjectiveParameterScheme f).hom g h
    have hq : q ≫ (surjectiveParameterScheme f).hom = g :=
      Albanese.Construction.ReducedFactor.factorThroughClosed_comp _ _ h
    exact ⟨q, hq, fun r hr ↦ (cancel_mono (surjectiveParameterScheme f).hom).mp
      (hr.trans hq.symm)⟩
  · rintro ⟨q, hq, _⟩
    rw [← hq]
    rintro b ⟨s, rfl⟩
    rw [← surjectiveParameterScheme_range]
    exact ⟨q s, rfl⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SurjectiveLocus
