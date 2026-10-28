import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf
import OAI.Analysis.DifferentialForms.Manifold.OpenDeRham
import Mathlib.Algebra.Homology.Additive

/-! # Sheaf De Rham -/

namespace OAI.Analysis.DifferentialForms.Manifold.SheafDeRham

noncomputable section

/-!
The de Rham complex of sheaves of genuine smooth manifold forms. Its sections
on an open set recover the open-domain de Rham complex, and its global sections
recover the already constructed global manifold de Rham complex. No resolution
property or comparison with singular cohomology is assumed.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

universe u v w

section SectionsFunctor

variable {X : Type v} [TopologicalSpace X]

/-- Taking sections of a complex-module sheaf on an actual open set. -/
def complexModuleSheafSections (U : Opens X) :
    TopCat.Sheaf (ModuleCat.{w} ℂ) (TopCat.of X) ⥤ ModuleCat.{w} ℂ where
  obj F := F.presheaf.obj (op U)
  map f := f.hom.app (op U)
  map_id _ := rfl
  map_comp _ _ := rfl

instance complexModuleSheafSections_preservesZeroMorphisms (U : Opens X) :
    (complexModuleSheafSections U :
      TopCat.Sheaf (ModuleCat.{w} ℂ) (TopCat.of X) ⥤ ModuleCat.{w} ℂ).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Sheaf restriction is a natural transformation between section functors. -/
def complexModuleSheafRestriction {U V : Opens X} (h : V ≤ U) :
    (complexModuleSheafSections U :
      TopCat.Sheaf (ModuleCat.{w} ℂ) (TopCat.of X) ⥤ ModuleCat.{w} ℂ) ⟶
      complexModuleSheafSections V where
  app F := F.presheaf.map (homOfLE h).op
  naturality _ _ f := (f.hom.naturality (homOfLE h).op).symm

end SectionsFunctor

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type v) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual cochain complex of sheaves of smooth manifold forms. -/
def manifoldDeRhamSheafComplex :
    CochainComplex (TopCat.Sheaf (ModuleCat.{max u v} ℂ) (TopCat.of M)) ℕ :=
  CochainComplex.of (ManifoldSheaf.manifoldFormSheaf E M) (ManifoldSheaf.manifoldFormSheafD E M)
    (ManifoldSheaf.manifoldFormSheafD_squared E M)

@[simp]
theorem manifoldDeRhamSheafComplex_X (n : ℕ) :
    (manifoldDeRhamSheafComplex E M).X n = ManifoldSheaf.manifoldFormSheaf E M n := rfl

@[simp]
theorem manifoldDeRhamSheafComplex_d (n : ℕ) :
    (manifoldDeRhamSheafComplex E M).d n (n + 1) = ManifoldSheaf.manifoldFormSheafD E M n :=
  CochainComplex.of_d (ManifoldSheaf.manifoldFormSheaf E M) (ManifoldSheaf.manifoldFormSheafD E M) n

variable {M}

/-- Apply the sections functor to the genuine manifold de Rham sheaf complex. -/
def manifoldDeRhamSheafSectionsComplex (U : Opens M) :
    CochainComplex (ModuleCat.{max u v} ℂ) ℕ :=
  ((complexModuleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (manifoldDeRhamSheafComplex E M)

@[simp]
theorem manifoldDeRhamSheafSectionsComplex_X (U : Opens M) (n : ℕ) :
    (manifoldDeRhamSheafSectionsComplex E U).X n =
      ModuleCat.of ℂ (Open.SmoothOpenManifoldForm E U n) := rfl

@[simp]
theorem manifoldDeRhamSheafSectionsComplex_d (U : Opens M) (n : ℕ) :
    (manifoldDeRhamSheafSectionsComplex E U).d n (n + 1) =
      ModuleCat.ofHom (Open.SmoothOpenManifoldForm.d (E := E) (U := U) (n := n)) := by
  change (complexModuleSheafSections U).map
    ((manifoldDeRhamSheafComplex E M).d n (n + 1)) = _
  rw [manifoldDeRhamSheafComplex_d]
  rfl

/-- Open sections of the sheaf complex are exactly the open-domain complex. -/
theorem manifoldDeRhamSheafSectionsComplex_eq (U : Opens M) :
    manifoldDeRhamSheafSectionsComplex E U = OpenDeRham.openManifoldDeRhamComplex E U := by
  refine HomologicalComplex.ext rfl ?_
  intro i j hij
  obtain rfl := (show i + 1 = j from hij)
  rw [manifoldDeRhamSheafSectionsComplex_d, OpenDeRham.openManifoldDeRhamComplex_d]
  rfl

/-- The open-section comparison is the identity on each genuine form space. -/
def manifoldDeRhamSheafSectionsIso (U : Opens M) :
    manifoldDeRhamSheafSectionsComplex E U ≅ OpenDeRham.openManifoldDeRhamComplex E U :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    obtain rfl := (show i + 1 = j from hij)
    rw [manifoldDeRhamSheafSectionsComplex_d, OpenDeRham.openManifoldDeRhamComplex_d]
    rfl)

/-- Restriction of the sheaf complex after taking sections. -/
def manifoldDeRhamSheafRestriction {U V : Opens M} (h : V ≤ U) :
    manifoldDeRhamSheafSectionsComplex E U ⟶ manifoldDeRhamSheafSectionsComplex E V :=
  ((complexModuleSheafRestriction h).mapHomologicalComplex (ComplexShape.up ℕ)).app
    (manifoldDeRhamSheafComplex E M)

/-- The identification with open-domain forms preserves actual restriction. -/
theorem manifoldDeRhamSheafSectionsIso_restrict {U V : Opens M} (h : V ≤ U) :
    (manifoldDeRhamSheafSectionsIso E U).hom ≫ OpenDeRham.openManifoldDeRhamRestrict E h =
      manifoldDeRhamSheafRestriction E h ≫ (manifoldDeRhamSheafSectionsIso E V).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  rfl

variable (M)

/-- The global sections of the sheaf complex are the global manifold de Rham complex. -/
def manifoldDeRhamGlobalSectionsIso :
    manifoldDeRhamSheafSectionsComplex E (⊤ : Opens M) ≅ ManifoldDeRham.manifoldDeRhamComplex E M :=
  HomologicalComplex.Hom.isoOfComponents (fun n => ManifoldSheaf.manifoldFormGlobalSectionsIso E M n) (by
    intro i j hij
    obtain rfl := (show i + 1 = j from hij)
    rw [manifoldDeRhamSheafSectionsComplex_d, ManifoldDeRham.manifoldDeRhamComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact Open.SmoothOpenManifoldForm.toGlobal_d form)

@[simp]
theorem manifoldDeRhamGlobalSectionsIso_hom_f_apply (n : ℕ)
    (form : Open.SmoothOpenManifoldForm E (⊤ : Opens M) n) :
    ((manifoldDeRhamGlobalSectionsIso E M).hom.f n) form =
      Open.SmoothOpenManifoldForm.toGlobal form := rfl

@[simp]
theorem manifoldDeRhamGlobalSectionsIso_inv_f_apply (n : ℕ)
    (form : Manifold.Algebra.SmoothManifoldForm E M n) :
    ((manifoldDeRhamGlobalSectionsIso E M).inv.f n) form =
      Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form := rfl

/-- Cohomology of the global section complex is genuine global de Rham cohomology. -/
def manifoldDeRhamGlobalSectionsCohomologyIso (n : ℕ) :
    (manifoldDeRhamSheafSectionsComplex E (⊤ : Opens M)).homology n ≅
      ManifoldDeRham.manifoldDeRhamCohomology E M n :=
  HomologicalComplex.homologyMapIso (manifoldDeRhamGlobalSectionsIso E M) n

/-- Global forms and forms on the top open set give canonically isomorphic complexes. -/
def manifoldDeRhamTopIso :
    ManifoldDeRham.manifoldDeRhamComplex E M ≅ OpenDeRham.openManifoldDeRhamComplex E (⊤ : Opens M) :=
  (manifoldDeRhamGlobalSectionsIso E M).symm ≪≫
    manifoldDeRhamSheafSectionsIso E (⊤ : Opens M)

@[simp]
theorem manifoldDeRhamTopIso_hom :
    (manifoldDeRhamTopIso E M).hom = OpenDeRham.manifoldDeRhamOnOpen E (⊤ : Opens M) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  rfl

/-- The global and top-open de Rham cohomologies agree through their actual forms. -/
def manifoldDeRhamCohomologyTopIso (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamCohomology E M n ≅ OpenDeRham.openManifoldDeRhamCohomology E (⊤ : Opens M) n :=
  HomologicalComplex.homologyMapIso (manifoldDeRhamTopIso E M) n

/-- The global-section identification respects restriction to every open domain. -/
theorem manifoldDeRhamGlobalSectionsIso_restrict (U : Opens M) :
    (manifoldDeRhamGlobalSectionsIso E M).hom ≫ OpenDeRham.manifoldDeRhamOnOpen E U =
      manifoldDeRhamSheafRestriction E (show U ≤ ⊤ from le_top) ≫
        (manifoldDeRhamSheafSectionsIso E U).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  exact Open.SmoothOpenManifoldForm.toGlobal_apply form x

end

end OAI.Analysis.DifferentialForms.Manifold.SheafDeRham
