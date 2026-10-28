import OAI.AlgebraicTopology.Cohomology.Singular.SmoothStalkComparison
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections
import OAI.AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex
import OAI.AlgebraicTopology.Cohomology.Singular.CechDoubleComplex
import OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation
import OAI.AlgebraicTopology.DeRham.Comparison.CechColumns

/-! # Smooth Cech Restriction -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmoothCechRestriction

noncomputable section

/-!
# Actual continuous-to-smooth restriction on Čech total complexes

The map is induced by restricting ordinary singular cochains to the actual
manifold-smooth simplices on each open intersection. The global augmentation
compatibilities identify the genuine cochains on the whole space with the
canonical top-section presentation used by the Čech total functor.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section OrdinaryTop

variable (X : TopCat.{0}) {J : Type} (U : J → Opens X) (A : ModuleCat.{0} ℂ)

/-- The canonical top-section isomorphism has literal restriction along the
top open inclusion as its inverse. -/
@[simp]
theorem singularCochainPresheafTopIso_inv :
    (DeRham.Comparison.SingularPresheaf.singularCochainPresheafTopIso A X).inv =
      Functor.singularPullback A (Opens.inclusion' (⊤ : Opens X)) := rfl

/-- The ordinary global column augmentation is actual top restriction
followed by the generic section augmentation. -/
theorem globalSingularCechColumnAugmentation_eq_top :
    CechDoubleComplex.globalSingularCechColumnAugmentation X U A =
      (DeRham.Comparison.SingularPresheaf.singularCochainPresheafTopIso A X).inv ≫
        DeRham.Comparison.CechComplexAugmentation.cechColumnAugmentation U ⊤ (fun _ => le_top) (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext a
  rw [CechDoubleComplex.globalSingularCechColumnAugmentation_apply]
  let f : TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶ TopCat.of (⊤ : Opens X) :=
    (Opens.toTopCat X).map (homOfLE (DeRham.Comparison.CechComplexAugmentation.cechIntersection_le_openDomain U ⊤ (fun _ => le_top) a))
  let g : TopCat.of (⊤ : Opens X) ⟶ X := Opens.inclusion' (⊤ : Opens X)
  have h := congrArg (fun k => k.f n) (Functor.singularPullback_comp A f g)
  exact ConcreteCategory.congr_hom h c

/-- The installed ordinary global total augmentation agrees with its
canonical presentation through actual sections on the top open set. -/
theorem globalSingularCechAugmentation_eq_top :
    CechDoubleComplex.globalSingularCechAugmentation X U A =
      (DeRham.Comparison.SingularPresheaf.singularCochainPresheafTopIso A X).inv ≫
        DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation U ⊤ (fun _ => le_top) (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [CechDoubleComplex.globalSingularCechAugmentation_f, HomologicalComplex.comp_f,
    DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation_f, globalSingularCechColumnAugmentation_eq_top,
    HomologicalComplex.comp_f]
  exact Category.assoc _ _ _

end OrdinaryTop

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (X : Type) [TopologicalSpace X] [ChartedSpace E X]
variable {J : Type} (U : J → Opens X) (A : ModuleCat.{0} ℂ)

/-- Evaluation on the top open and restriction to smooth simplices commute
with the actual inclusion of that open into the whole space. -/
theorem manifoldSmoothCochainRestriction_top_naturality :
    (DeRham.Comparison.SingularPresheaf.singularCochainPresheafTopIso A (TopCat.of X)).inv ≫
        DeRham.Comparison.CechComplexAugmentation.presheafComplexSectionsMap ⊤ (SmoothStalkComparison.manifoldSmoothPresheafRestriction E X A) =
      ManifoldSmooth.manifoldSmoothCochainRestriction E A X ≫
        ManifoldSmoothFunctor.manifoldSmoothPullback E E A (Subtype.val : (⊤ : Opens X) → X)
          (contMDiff_subtype_val (I := 𝓘(ℝ, E))) :=
  ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality A
    (Subtype.val : (⊤ : Opens X) → X)
    (contMDiff_subtype_val (I := 𝓘(ℝ, E)))

/-- The inverse canonical top identifications intertwine the genuine
presheaf restriction and the genuine restriction on the whole manifold. -/
theorem manifoldSmoothPresheafRestriction_top_inv :
    (DeRham.Comparison.SingularPresheaf.singularCochainPresheafTopIso A (TopCat.of X)).inv ≫
        DeRham.Comparison.CechComplexAugmentation.presheafComplexSectionsMap ⊤ (SmoothStalkComparison.manifoldSmoothPresheafRestriction E X A) =
      ManifoldSmooth.manifoldSmoothCochainRestriction E A X ≫
        (ManifoldSmoothSections.manifoldSmoothPresheafTopIso E X A).inv := by
  rw [ManifoldSmoothSections.manifoldSmoothPresheafTopIso_inv]
  exact manifoldSmoothCochainRestriction_top_naturality E X A

/-- After the canonical top identifications, restriction of presheaf
sections is exactly restriction of cochains on the whole manifold. -/
theorem manifoldSmoothPresheafRestriction_top :
    DeRham.Comparison.CechComplexAugmentation.presheafComplexSectionsMap ⊤ (SmoothStalkComparison.manifoldSmoothPresheafRestriction E X A) ≫
        (ManifoldSmoothSections.manifoldSmoothPresheafTopIso E X A).hom =
      (DeRham.Comparison.SingularPresheaf.singularCochainPresheafTopIso A (TopCat.of X)).hom ≫
        ManifoldSmooth.manifoldSmoothCochainRestriction E A X := by
  apply (cancel_epi (DeRham.Comparison.SingularPresheaf.singularCochainPresheafTopIso A (TopCat.of X)).inv).mp
  rw [← Category.assoc, manifoldSmoothPresheafRestriction_top_inv]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- Restriction to manifold-smooth simplices on every actual Čech intersection. -/
abbrev manifoldSmoothCechDoubleRestriction :
    CechDoubleComplex.singularCechDoubleComplex (TopCat.of X) U A ⟶
      SmoothCechDoubleComplex.manifoldSmoothCechDoubleComplex E X U A :=
  DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplexMap U (SmoothStalkComparison.manifoldSmoothPresheafRestriction E X A)

/-- On each intersection the coefficient cochain map is exactly the installed
ordinary-to-manifold-smooth restriction. -/
@[simp]
theorem manifoldSmoothCechRestriction_intersection {p : ℕ} (a : Fin (p + 1) → J) :
    DeRham.Comparison.CechColumns.cechIntersectionMap U (SmoothStalkComparison.manifoldSmoothPresheafRestriction E X A) a =
      ManifoldSmooth.manifoldSmoothCochainRestriction E A (DeRham.Comparison.SmoothCech.cechIntersection U a) := rfl

/-- The double-complex map evaluates by the genuine restriction on the
corresponding open intersection. -/
@[simp]
theorem manifoldSmoothCechDoubleRestriction_apply (p q : ℕ)
    (c : DeRham.Comparison.SmoothCech.CechCochain (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A (TopCat.of X) q) U p)
    (a : Fin (p + 1) → J) :
    (((manifoldSmoothCechDoubleRestriction E X U A).f p).f q c) a =
      (ManifoldSmooth.manifoldSmoothCochainRestriction E A (DeRham.Comparison.SmoothCech.cechIntersection U a)).f q (c a) := rfl

/-- The actual induced restriction between the signed Čech total complexes. -/
def manifoldSmoothCechRestriction :
    CechDoubleComplex.singularCechTotal (TopCat.of X) U A ⟶
      SmoothCechDoubleComplex.manifoldSmoothCechTotal E X U A :=
  DeRham.Comparison.CechTotalFunctor.cechTotalMap U (SmoothStalkComparison.manifoldSmoothPresheafRestriction E X A)

/-- On every total-complex summand the map is the given cochain restriction
on all actual intersection sections. -/
theorem manifoldSmoothCechRestriction_iota (p q n : ℕ) (h : p + q = n) :
    DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of X)) p q n h ≫
        (manifoldSmoothCechRestriction E X U A).f n =
      ModuleCat.ofHom (DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap U
        ((SmoothStalkComparison.manifoldSmoothPresheafRestriction E X A).f q) p) ≫
          DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X A) p q n h :=
  DeRham.Comparison.CechTotalFunctor.cechTotalInclusion_map U (SmoothStalkComparison.manifoldSmoothPresheafRestriction E X A) p q n h

/-- The actual global restriction commutes with the canonical presentation
of the smooth total augmentation through the top open subset. -/
theorem manifoldSmoothCechRestriction_top_augmentation :
    ManifoldSmooth.manifoldSmoothCochainRestriction E A X ≫
        (ManifoldSmoothFunctor.manifoldSmoothPullback E E A (Subtype.val : (⊤ : Opens X) → X)
          (contMDiff_subtype_val (I := 𝓘(ℝ, E))) ≫
          DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation U ⊤ (fun _ => le_top)
            (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X A)) =
      CechDoubleComplex.globalSingularCechAugmentation (TopCat.of X) U A ≫
        manifoldSmoothCechRestriction E X U A := by
  rw [← Category.assoc, ← manifoldSmoothCochainRestriction_top_naturality,
    Category.assoc, DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation_naturality, ← Category.assoc,
    ← globalSingularCechAugmentation_eq_top]
  rfl

/-- The actual global ordinary-to-smooth restriction commutes with the
installed global Čech augmentations and the actual total restriction. -/
theorem manifoldSmoothCechRestriction_augmentation :
    ManifoldSmooth.manifoldSmoothCochainRestriction E A X ≫
        SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E X U A =
      CechDoubleComplex.globalSingularCechAugmentation (TopCat.of X) U A ≫
        manifoldSmoothCechRestriction E X U A := by
  rw [SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation_eq_top, ManifoldSmoothSections.manifoldSmoothPresheafTopIso_inv]
  exact manifoldSmoothCechRestriction_top_augmentation E X U A

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmoothCechRestriction
