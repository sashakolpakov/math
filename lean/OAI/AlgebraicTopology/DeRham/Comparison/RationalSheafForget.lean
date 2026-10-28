import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.Functor
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Rational Sheaf Forget -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RationalSheafForget

noncomputable section

/-!
# Forgetting rational scalars on actual sheaves and cochain complexes

The functor is literal postcomposition by `ModuleCat ℚ ⥤ AddCommGrpCat`.
It preserves finite limits and epimorphisms, hence homology. Sections commute
with it by their actual evaluation definitions. These facts do not assume
that the global-sections functor is exact.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- The ordinary forgetful functor on rational modules. -/
abbrev rationalForget : ModuleCat.{u,0} ℚ ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u,0} ℚ) AddCommGrpCat.{u}

/-- Additive maps between rational modules are automatically rational-linear. -/
instance rationalForget_full : rationalForget.Full where
  map_surjective {M N} f := by
    let a : M →+ N := f.hom
    exact ⟨ModuleCat.ofHom a.toRatLinearMap, rfl⟩

instance rationalModules_haveLimits :
    HasLimitsOfSize.{u,u} (ModuleCat.{u,0} ℚ) :=
  ModuleCat.hasLimitsOfSize.{u,u,u,0}

instance rationalModules_forgetFiltered :
    PreservesFilteredColimits (forget (ModuleCat.{u,0} ℚ)) :=
  Limits.comp_preservesFilteredColimits rationalForget (forget AddCommGrpCat.{u})

/-- Forgetting rational scalars is literal composition of each sheaf with the
ordinary forgetful functor. -/
def rationalSheafForget (X : TopCat.{u}) :
    TopCat.Sheaf (ModuleCat.{u,0} ℚ) X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  sheafCompose (Opens.grothendieckTopology X) rationalForget

@[simp]
theorem rationalSheafForget_obj_obj (X : TopCat.{u})
    (F : TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) :
    ((rationalSheafForget X).obj F).obj = F.obj ⋙ rationalForget := rfl

instance rationalSheafForget_additive (X : TopCat.{u}) :
    (rationalSheafForget X).Additive where
  map_add := rfl

instance rationalSheafForget_faithful (X : TopCat.{u}) :
    (rationalSheafForget X).Faithful :=
  inferInstanceAs (sheafCompose (Opens.grothendieckTopology X) rationalForget).Faithful

instance rationalSheafForget_full (X : TopCat.{u}) :
    (rationalSheafForget X).Full :=
  inferInstanceAs (sheafCompose (Opens.grothendieckTopology X) rationalForget).Full

/-- Limits of sheaves are detected on their underlying presheaves. -/
instance rationalSheafForget_preservesFiniteLimits (X : TopCat.{u}) :
    PreservesFiniteLimits (rationalSheafForget X) where
  preservesFiniteLimits J _ _ := by
    have : PreservesLimitsOfShape J
        (rationalSheafForget X ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X) := by
      change PreservesLimitsOfShape J
        (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u,0} ℚ) ⋙
          (Functor.whiskeringRight (Opens X)ᵒᵖ (ModuleCat.{u,0} ℚ)
            AddCommGrpCat.{u}).obj rationalForget)
      have : PreservesLimitsOfShape J
          (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u,0} ℚ)) := by
        infer_instance
      have : PreservesLimitsOfShape J
          ((Functor.whiskeringRight (Opens X)ᵒᵖ (ModuleCat.{u,0} ℚ)
            AddCommGrpCat.{u}).obj rationalForget) := by
        infer_instance
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (rationalSheafForget X) (TopCat.Sheaf.forget AddCommGrpCat.{u} X)

/-- Forgetting scalars leaves the local preimage condition unchanged, and so
preserves epimorphisms of actual sheaves. -/
instance rationalSheafForget_preservesEpimorphisms (X : TopCat.{u}) :
    (rationalSheafForget X).PreservesEpimorphisms where
  preserves {F G} f hf := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi ((rationalSheafForget X).map f)).mp
    have h := (TopCat.Sheaf.isLocallySurjective_iff_epi f).mpr hf
    constructor
    intro U s
    exact h.imageSieve_mem s

/-- The genuine rational-to-additive sheaf functor is exact. -/
instance rationalSheafForget_preservesHomology (X : TopCat.{u}) :
    (rationalSheafForget X).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (rationalSheafForget X)

/-- Flasqueness survives forgetting the rational module structure. -/
instance rationalSheafForget_isFlasque {X : TopCat.{u}}
    (F : TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque ((rationalSheafForget X).obj F) where
  epi i := by
    change Epi (rationalForget.map (F.obj.map i))
    infer_instance

/-- Apply the actual sheaf forgetful functor in every cochain degree. -/
def rationalSheafForgetComplex {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  ((rationalSheafForget X).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- Exactness gives the canonical comparison of genuine homology sheaves. -/
def rationalSheafForgetHomologyIso {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ) (n : ℕ) :
    (rationalSheafForgetComplex K).homology n ≅
      (rationalSheafForget X).obj (K.homology n) :=
  (K.sc n).mapHomologyIso (rationalSheafForget X)

/-- The homology-sheaf comparison commutes with actual cochain maps. -/
theorem rationalSheafForgetHomologyIso_naturality {X : TopCat.{u}}
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ}
    (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((rationalSheafForget X).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫
      (rationalSheafForgetHomologyIso L n).hom =
      (rationalSheafForgetHomologyIso K n).hom ≫
        (rationalSheafForget X).map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f) (rationalSheafForget X)

/-- Forgetting rational scalars both preserves and detects sheaf exactness. -/
theorem rationalSheafForgetComplex_exactAt_iff {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ) (n : ℕ) :
    (rationalSheafForgetComplex K).ExactAt n ↔ K.ExactAt n :=
  (K.sc n).exact_map_iff_of_faithful (rationalSheafForget X)

/-- Rational-valued sections on an actual open set. -/
def rationalSheafSections {X : TopCat.{u}} (U : Opens X) :
    TopCat.Sheaf (ModuleCat.{u,0} ℚ) X ⥤ ModuleCat.{u,0} ℚ :=
  TopCat.Sheaf.forget (ModuleCat.{u,0} ℚ) X ⋙
    (evaluation (Opens X)ᵒᵖ (ModuleCat.{u,0} ℚ)).obj (op U)

/-- Additive-group-valued sections on the same actual open set. -/
def additiveSheafSections {X : TopCat.{u}} (U : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

instance rationalSheafSections_additive {X : TopCat.{u}} (U : Opens X) :
    (rationalSheafSections U).Additive where
  map_add := rfl

instance additiveSheafSections_additive {X : TopCat.{u}} (U : Opens X) :
    (additiveSheafSections U).Additive where
  map_add := rfl

/-- Taking sections commutes with forgetting scalars by evaluation. -/
def rationalSheafForgetSectionsIso {X : TopCat.{u}} (U : Opens X) :
    rationalSheafForget X ⋙ additiveSheafSections U ≅
      rationalSheafSections U ⋙ rationalForget :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro F G f
    change rationalForget.map (f.hom.app (op U)) ≫ 𝟙 _ =
      𝟙 _ ≫ rationalForget.map (f.hom.app (op U))
    simp only [Category.comp_id, Category.id_comp])

/-- The actual rational complex of sections on an open set. -/
def rationalSheafSectionsComplex {X : TopCat.{u}} (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ) :
    CochainComplex (ModuleCat.{u,0} ℚ) ℕ :=
  ((rationalSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- The actual additive complex of sections on an open set. -/
def additiveSheafSectionsComplex {X : TopCat.{u}} (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  ((additiveSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- The sections comparison commutes with the actual cochain differentials. -/
def rationalSheafForgetSectionsComplexIso {X : TopCat.{u}} (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ) :
    additiveSheafSectionsComplex U (rationalSheafForgetComplex K) ≅
      ((rationalForget.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (rationalSheafSectionsComplex U K)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j _
    change rationalForget.map ((K.d i j).hom.app (op U)) ≫ 𝟙 _ =
      𝟙 _ ≫ rationalForget.map ((K.d i j).hom.app (op U))
    simp only [Category.comp_id, Category.id_comp])

/-- The section-complex comparison is natural in the rational sheaf complex. -/
theorem rationalSheafForgetSectionsComplexIso_naturality {X : TopCat.{u}}
    (U : Opens X)
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ} (f : K ⟶ L) :
    ((additiveSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (((rationalSheafForget X).mapHomologicalComplex (ComplexShape.up ℕ)).map f) ≫
      (rationalSheafForgetSectionsComplexIso U L).hom =
      (rationalSheafForgetSectionsComplexIso U K).hom ≫
        (rationalForget.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (((rationalSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change rationalForget.map ((f.f n).hom.app (op U)) ≫ 𝟙 _ =
    𝟙 _ ≫ rationalForget.map ((f.f n).hom.app (op U))
  simp only [Category.comp_id, Category.id_comp]

/-- Forgetting scalars commutes with the ordinary homology of a rational
cochain complex because the ordinary module forgetful functor is exact. -/
def rationalForgetHomologyIso
    (K : CochainComplex (ModuleCat.{u,0} ℚ) ℕ) (n : ℕ) :
    ((rationalForget.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ≅
      rationalForget.obj (K.homology n) :=
  (K.sc n).mapHomologyIso rationalForget

/-- Ordinary homology commutes naturally with forgetting rational scalars. -/
theorem rationalForgetHomologyIso_naturality
    {K L : CochainComplex (ModuleCat.{u,0} ℚ) ℕ} (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((rationalForget.mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫
      (rationalForgetHomologyIso L n).hom =
      (rationalForgetHomologyIso K n).hom ≫
        rationalForget.map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f) rationalForget

/-- The comparison on homology of sections is induced by the actual complex
comparison and the exact module forgetful functor. -/
def rationalSectionsForgetHomologyIso {X : TopCat.{u}} (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ) (n : ℕ) :
    rationalForget.obj ((rationalSheafSectionsComplex U K).homology n) ≅
      (additiveSheafSectionsComplex U (rationalSheafForgetComplex K)).homology n :=
  (rationalForgetHomologyIso (rationalSheafSectionsComplex U K) n).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).mapIso
      (rationalSheafForgetSectionsComplexIso U K).symm

end

end OAI.AlgebraicTopology.DeRham.Comparison.RationalSheafForget
