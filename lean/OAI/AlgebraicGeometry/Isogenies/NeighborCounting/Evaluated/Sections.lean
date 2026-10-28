import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Targets
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Sections -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Sections.Lifts

noncomputable section

/-!
Evaluated points of a proper group over a valuation ring extend uniquely,
and the extension preserves multiplication and every torsion bound. This
applies to the evaluated finite flat torsion schemes of the lifted source.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable (R L : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
variable (A : Over (Spec (.of R))) [GrpObj A] [IsProper A.hom]

def genericTest : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L)))

/-- Restriction of integral sections to the generic point. -/
def sectionRestriction : ((𝟙_ (Over (Spec (.of R)))) ⟶ A) →*
    (genericTest R L ⟶ A) where
  toFun s := toUnit (genericTest R L) ≫ s
  map_one' := MonObj.comp_one _
  map_mul' s t := MonObj.comp_mul _ s t

theorem sectionRestriction_bijective : Function.Bijective (sectionRestriction R L A) := by
  constructor
  · intro s t h
    have hs : s.left ≫ A.hom = 𝟙 (Spec (.of R)) := s.w
    have ht : t.left ≫ A.hom = 𝟙 (Spec (.of R)) := t.w
    have hz : (toUnit (genericTest R L) ≫ s).left ≫ A.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ 𝟙 (Spec (.of R)) := by
      exact ((toUnit (genericTest R L) ≫ s).w).trans (Category.comp_id _).symm
    obtain ⟨l, _, hu⟩ := Targets.Lifts.proper_evaluated_extension A.hom (𝟙 (Spec (.of R)))
      (toUnit (genericTest R L) ≫ s).left hz
    apply Over.OverMorphism.ext
    apply (hu s.left ⟨rfl, hs⟩).trans
    apply (hu t.left ⟨?_, ht⟩).symm
    exact congrArg (fun z : genericTest R L ⟶ A => z.left) h.symm
  · intro z
    have hz : z.left ≫ A.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ 𝟙 (Spec (.of R)) :=
      z.w.trans (Category.comp_id _).symm
    obtain ⟨l, hl, _⟩ := Targets.Lifts.proper_evaluated_extension A.hom (𝟙 (Spec (.of R))) z.left hz
    refine ⟨Over.homMk l hl.2, ?_⟩
    apply Over.OverMorphism.ext
    exact hl.1

/-- Unique extension is a group isomorphism on sections. In particular,
all algebraic relations among evaluated torsion labels extend integrally. -/
def evaluatedSectionsEquiv : ((𝟙_ (Over (Spec (.of R)))) ⟶ A) ≃*
    (genericTest R L ⟶ A) :=
  MulEquiv.ofBijective (sectionRestriction R L A) (sectionRestriction_bijective R L A)

theorem evaluated_extension_torsion (z : genericTest R L ⟶ A) (n : ℕ) (hz : z ^ n = 1) :
    ((evaluatedSectionsEquiv R L A).symm z) ^ n = 1 := by
  rw [← map_pow, hz, map_one]

/-- An evaluated group of generic labels gives integral sections by
construction, with the full group law preserved. -/
def extendEvaluatedLabels {G : Type u} [Group G] (z : G →* (genericTest R L ⟶ A)) :
    G →* ((𝟙_ (Over (Spec (.of R)))) ⟶ A) :=
  (evaluatedSectionsEquiv R L A).symm.toMonoidHom.comp z

theorem extendEvaluatedLabels_generic {G : Type u} [Group G]
    (z : G →* (genericTest R L ⟶ A)) (g : G) :
    sectionRestriction R L A (extendEvaluatedLabels R L A z g) = z g :=
  (evaluatedSectionsEquiv R L A).apply_symm_apply (z g)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Sections.Lifts
