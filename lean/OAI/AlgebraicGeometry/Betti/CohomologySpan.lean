import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Homotopy

/-! # Cohomology Span -/

namespace OAI.AlgebraicGeometry.Betti.CohomologySpan.Realization

noncomputable section

/-!
# Canonical cohomology comparisons from a span

The isomorphism is obtained from the actual maps of a span of cochain
complexes, after those maps have been proved to be quasi-isomorphisms. Its
commuting square determines it uniquely. Commuting maps of spans, including
refinements of a common comparison complex, preserve the induced map.
-/

open _root_.CategoryTheory

universe u v

section General

variable {D : Type u} [Category.{v} D] [Abelian D]
  {A B C A' B' C' : CochainComplex D ℕ}

/-- The comparison induced by the actual span `A → B ← C`. -/
def cohomologySpanIso (f : A ⟶ B) (g : C ⟶ B) [QuasiIso f] [QuasiIso g] (n : ℕ) :
    A.homology n ≅ C.homology n :=
  asIso (HomologicalComplex.homologyMap f n) ≪≫
    (asIso (HomologicalComplex.homologyMap g n)).symm

/-- The defining commuting square of the comparison. -/
@[reassoc]
theorem cohomologySpanIso_hom_comp (f : A ⟶ B) (g : C ⟶ B)
    [QuasiIso f] [QuasiIso g] (n : ℕ) :
    (cohomologySpanIso f g n).hom ≫ HomologicalComplex.homologyMap g n =
      HomologicalComplex.homologyMap f n := by
  simp [cohomologySpanIso]

/-- This square characterizes the forward comparison uniquely. -/
theorem cohomologySpanIso_hom_unique (f : A ⟶ B) (g : C ⟶ B)
    [QuasiIso f] [QuasiIso g] (n : ℕ)
    (h : A.homology n ⟶ C.homology n)
    (hh : h ≫ HomologicalComplex.homologyMap g n = HomologicalComplex.homologyMap f n) :
    h = (cohomologySpanIso f g n).hom := by
  apply (cancel_mono (HomologicalComplex.homologyMap g n)).mp
  rw [hh, cohomologySpanIso_hom_comp]

/-- Reversing the legs reverses the canonical comparison. -/
theorem cohomologySpanIso_symm (f : A ⟶ B) (g : C ⟶ B)
    [QuasiIso f] [QuasiIso g] (n : ℕ) :
    (cohomologySpanIso f g n).symm = cohomologySpanIso g f n := by
  apply Iso.ext
  simp [cohomologySpanIso]

/-- Every commuting map of actual spans induces a commuting square on the
canonical cohomology comparisons. No invertibility of the middle map is needed. -/
@[reassoc]
theorem cohomologySpanIso_naturality
    (f : A ⟶ B) (g : C ⟶ B) (f' : A' ⟶ B') (g' : C' ⟶ B')
    [QuasiIso f] [QuasiIso g] [QuasiIso f'] [QuasiIso g']
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (hf : f ≫ b = a ≫ f') (hg : g ≫ b = c ≫ g') (n : ℕ) :
    (cohomologySpanIso f g n).hom ≫ HomologicalComplex.homologyMap c n =
      HomologicalComplex.homologyMap a n ≫ (cohomologySpanIso f' g' n).hom := by
  have hfH : HomologicalComplex.homologyMap f n ≫ HomologicalComplex.homologyMap b n =
      HomologicalComplex.homologyMap a n ≫ HomologicalComplex.homologyMap f' n := by
    rw [← HomologicalComplex.homologyMap_comp, hf, HomologicalComplex.homologyMap_comp]
  have hgH : HomologicalComplex.homologyMap g n ≫ HomologicalComplex.homologyMap b n =
      HomologicalComplex.homologyMap c n ≫ HomologicalComplex.homologyMap g' n := by
    rw [← HomologicalComplex.homologyMap_comp, hg, HomologicalComplex.homologyMap_comp]
  apply (cancel_mono (HomologicalComplex.homologyMap g' n)).mp
  simp only [Category.assoc]
  rw [← hgH, ← Category.assoc, cohomologySpanIso_hom_comp,
    cohomologySpanIso_hom_comp, hfH]

/-- Replacing the middle comparison complex by a quasi-isomorphic refinement
leaves the comparison between the two endpoints exactly unchanged. -/
theorem cohomologySpanIso_refinement (f : A ⟶ B) (g : C ⟶ B)
    [QuasiIso f] [QuasiIso g] (b : B ⟶ B') [QuasiIso b] (n : ℕ) :
    cohomologySpanIso (f ≫ b) (g ≫ b) n = cohomologySpanIso f g n := by
  apply Iso.ext
  have h := cohomologySpanIso_naturality f g (f ≫ b) (g ≫ b)
    (𝟙 A) b (𝟙 C) (by simp) (by simp) n
  simpa only [HomologicalComplex.homologyMap_id, Category.comp_id, Category.id_comp] using h.symm

/-- Refinement squares that commute up to actual cochain homotopies still
give strictly commuting comparisons on cohomology. -/
theorem cohomologySpanIso_naturality_of_homotopy
    (f : A ⟶ B) (g : C ⟶ B) (f' : A' ⟶ B') (g' : C' ⟶ B')
    [QuasiIso f] [QuasiIso g] [QuasiIso f'] [QuasiIso g']
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (hf : Homotopy (f ≫ b) (a ≫ f')) (hg : Homotopy (g ≫ b) (c ≫ g')) (n : ℕ) :
    (cohomologySpanIso f g n).hom ≫ HomologicalComplex.homologyMap c n =
      HomologicalComplex.homologyMap a n ≫ (cohomologySpanIso f' g' n).hom := by
  have hfH := hf.homologyMap_eq n
  have hgH := hg.homologyMap_eq n
  simp only [HomologicalComplex.homologyMap_comp] at hfH hgH
  apply (cancel_mono (HomologicalComplex.homologyMap g' n)).mp
  simp only [Category.assoc]
  rw [← hgH, ← Category.assoc, cohomologySpanIso_hom_comp,
    cohomologySpanIso_hom_comp, hfH]

/-- Homotopic choices of both legs induce exactly the same comparison. -/
theorem cohomologySpanIso_eq_of_homotopy
    (f f' : A ⟶ B) (g g' : C ⟶ B)
    [QuasiIso f] [QuasiIso g] [QuasiIso f'] [QuasiIso g']
    (hf : Homotopy f f') (hg : Homotopy g g') (n : ℕ) :
    cohomologySpanIso f g n = cohomologySpanIso f' g' n := by
  apply Iso.ext
  apply cohomologySpanIso_hom_unique f' g' n
  rw [← hg.homologyMap_eq n, cohomologySpanIso_hom_comp, hf.homologyMap_eq n]

end General

variable {R : Type} [Ring R] {A B C : CochainComplex (ModuleCat.{0} R) ℕ}

/-- The comparison sends a represented class to the unique class whose image
under the right leg is represented by the left leg of the original cocycle. -/
theorem cohomologySpanIso_map_class (f : A ⟶ B) (g : C ⟶ B)
    [QuasiIso f] [QuasiIso g] (n : ℕ) (x : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles A n) :
    HomologicalComplex.homologyMap g n
        ((cohomologySpanIso f g n).hom (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass A n x)) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass B n (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap f n x) := by
  have h := ConcreteCategory.congr_hom (cohomologySpanIso_hom_comp f g n)
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass A n x)
  exact h.trans (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality f n x)

/-- A concrete representative criterion: the comparison identifies two
cocycles exactly when their images differ by an actual boundary in the
middle complex. -/
theorem cohomologySpanIso_class_eq_iff (f : A ⟶ B) (g : C ⟶ B)
    [QuasiIso f] [QuasiIso g] (n : ℕ)
    (x : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles A n) (y : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles C n) :
    (cohomologySpanIso f g n).hom (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass A n x) =
        AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass C n y ↔
      ∃ z : (B.sc n).X₁, (B.sc n).f z = (f.f n) x.val - (g.f n) y.val := by
  have hinj : Function.Injective (HomologicalComplex.homologyMap g n) :=
    (asIso (HomologicalComplex.homologyMap g n)).toLinearEquiv.injective
  rw [← hinj.eq_iff, cohomologySpanIso_map_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality,
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists]
  rfl

end

end OAI.AlgebraicGeometry.Betti.CohomologySpan.Realization
