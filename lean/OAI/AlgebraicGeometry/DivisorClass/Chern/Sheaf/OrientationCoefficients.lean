import OAI.AlgebraicTopology.Cohomology.Singular.SheafGluing
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Orientation Coefficients -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.OrientationCoefficients

noncomputable section

section

/-!
# ChernClass: actual sections of an oriented sheaf supported on a closed subspace

A global section whose germ is a basis at every support point identifies
all sections with locally constant scalar functions on the support.
Local constancy follows from equality of actual germs. Surjectivity glues
scalar multiples of the original section with zero off the closed support.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.SheafGluing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {S : Type} [TopologicalSpace S]
variable (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (f : S → X)
variable (e : ∀ x, F.presheaf.stalk (f x) ≅ ModuleCat.of ℚ ℚ)

def sheafOrientationCoefficient
    (s : F.obj.obj (op (⊤ : Opens X))) (x : S) : ℚ :=
  (e x).hom (F.presheaf.germ ⊤ (f x) trivial s)

variable (σ : F.obj.obj (op (⊤ : Opens X)))
variable (hσ : ∀ x, sheafOrientationCoefficient F f e σ x = 1)

include σ hσ in
theorem sheafOrientationCoefficient_locallyConstant (hf : Continuous f)
    (s : F.obj.obj (op (⊤ : Opens X))) :
    IsLocallyConstant (sheafOrientationCoefficient F f e s) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  let q := sheafOrientationCoefficient F f e s x
  have hg : F.presheaf.germ ⊤ (f x) trivial s =
      F.presheaf.germ ⊤ (f x) trivial (q • σ) := by
    apply (e x).toLinearEquiv.injective
    change q = (e x).hom (F.presheaf.germ ⊤ (f x) trivial (q • σ))
    rw [map_smul, map_smul]
    change q = q * sheafOrientationCoefficient F f e σ x
    rw [hσ, mul_one]
  obtain ⟨U, hx, i, j, hu⟩ := F.presheaf.germ_eq (U := ⊤) (V := ⊤)
    (f x) trivial trivial s (q • σ) hg
  refine ⟨f ⁻¹' (U : Set X), U.isOpen.preimage hf, hx, ?_⟩
  intro y hy
  have hy' := congrArg (F.presheaf.germ U (f y) hy) hu
  simp only [TopCat.Presheaf.germ_res_apply] at hy'
  have hc := congrArg (e y).hom hy'
  rw [map_smul, map_smul] at hc
  change sheafOrientationCoefficient F f e s y =
    q * sheafOrientationCoefficient F f e σ y at hc
  simpa only [hσ, mul_one] using hc

def sheafOrientationCoefficients (hf : Continuous f) :
    F.obj.obj (op (⊤ : Opens X)) →ₗ[ℚ] LocallyConstant S ℚ where
  toFun s := ⟨sheafOrientationCoefficient F f e s,
    sheafOrientationCoefficient_locallyConstant F f e σ hσ hf s⟩
  map_add' s t := by
    apply LocallyConstant.ext
    intro x
    exact map_add ((F.presheaf.germ ⊤ (f x) trivial) ≫ (e x).hom).hom s t
  map_smul' q s := by
    apply LocallyConstant.ext
    intro x
    exact map_smul ((F.presheaf.germ ⊤ (f x) trivial) ≫ (e x).hom).hom q s

theorem sheafOrientationCoefficients_injective (hf : Continuous f)
    (hz : ∀ y, y ∉ Set.range f → IsZero (F.presheaf.stalk y)) :
    Function.Injective (sheafOrientationCoefficients F f e σ hσ hf) := by
  intro s t h
  apply TopCat.Presheaf.section_ext F ⊤
  intro y _
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    apply (e x).toLinearEquiv.injective
    exact congrArg (fun g : LocallyConstant S ℚ => g x) h
  · exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero (hz y hy)) _ _

end

/-! Locally constant coefficients glue to actual sections on the original closed support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.SheafGluing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {S : Type} [TopologicalSpace S]
variable (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (f : S → X)
variable (e : ∀ x, F.presheaf.stalk (f x) ≅ ModuleCat.of ℚ ℚ)
variable (σ : F.obj.obj (op (⊤ : Opens X)))
variable (hσ : ∀ x, sheafOrientationCoefficient F f e σ x = 1)

theorem sheafOrientationCoefficients_surjective (hf : Topology.IsClosedEmbedding f)
    (hz : ∀ y, y ∉ Set.range f → IsZero (F.presheaf.stalk y)) :
    Function.Surjective (sheafOrientationCoefficients F f e σ hσ hf.continuous) := by
  intro g
  have hopen (x : S) : ∃ U : Opens X,
      f x ∈ U ∧ ∀ y, f y ∈ U → g y = g x := by
    obtain ⟨U, hU, heq⟩ := hf.isInducing.isOpen_iff.mp (g.isLocallyConstant.isOpen_fiber (g x))
    refine ⟨⟨U, hU⟩, ?_, ?_⟩
    · change x ∈ f ⁻¹' U
      rw [heq]
      rfl
    · intro y hy
      have : y ∈ f ⁻¹' U := hy
      rwa [heq] at this
  choose U hx hval using hopen
  let O : Opens X := ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩
  let a (x : S) : F.obj.obj (op (U x)) :=
    g x • F.obj.map (homOfLE (le_top : U x ≤ ⊤)).op σ
  have hcover : iSup U ⊔ O = ⊤ := by
    apply top_unique
    intro y _
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hy
      exact Or.inl ((le_iSup U x) (hx x))
    · exact Or.inr hy
  have hcompat : ∀ i j (y : X) (hi : y ∈ U i) (hj : y ∈ U j),
      F.presheaf.germ (U i) y hi (a i) = F.presheaf.germ (U j) y hj (a j) := by
    intro i j y hi hj
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hy
      have hij : g i = g j := (hval i x hi).symm.trans (hval j x hj)
      simp only [a, map_smul, TopCat.Presheaf.germ_res_apply, hij]
    · exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero (hz y hy)) _ _
  obtain ⟨s, hs, _⟩ := AlgebraicTopology.Cohomology.Singular.SheafGluing.existsUnique_moduleSheafSection_with_zero F O U hcover a hcompat
    (fun y hy => hz y hy)
  refine ⟨s, ?_⟩
  apply LocallyConstant.ext
  intro x
  change sheafOrientationCoefficient F f e s x = g x
  have hg := congrArg (F.presheaf.germ (U x) (f x) (hx x)) (hs.1 x)
  simp only [a, map_smul, TopCat.Presheaf.germ_res_apply] at hg
  have hc := congrArg (e x).hom hg
  rw [map_smul] at hc
  change sheafOrientationCoefficient F f e s x =
    g x * sheafOrientationCoefficient F f e σ x at hc
  simpa only [hσ, mul_one] using hc

def sheafOrientationCoefficientsEquiv (hf : Topology.IsClosedEmbedding f)
    (hz : ∀ y, y ∉ Set.range f → IsZero (F.presheaf.stalk y)) :
    F.obj.obj (op (⊤ : Opens X)) ≃ₗ[ℚ] LocallyConstant S ℚ :=
  LinearEquiv.ofBijective (sheafOrientationCoefficients F f e σ hσ hf.continuous)
    ⟨sheafOrientationCoefficients_injective F f e σ hσ hf.continuous hz,
      sheafOrientationCoefficients_surjective F f e σ hσ hf hz⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.OrientationCoefficients
