import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.Functor
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Sheaf Forget -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.SheafForget

noncomputable section

/-! Literal forgetting of complex scalars preserves the actual sheaf homology constructions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

abbrev complexModuleForget : ModuleCat.{0} ℂ ⥤ AddCommGrpCat.{0} :=
  forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}

def complexSheafForget (X : TopCat.{0}) :
    TopCat.Sheaf (ModuleCat.{0} ℂ) X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
  sheafCompose (Opens.grothendieckTopology X) complexModuleForget

instance complexSheafForget_additive (X : TopCat.{0}) : (complexSheafForget X).Additive where
  map_add := rfl

instance complexSheafForget_faithful (X : TopCat.{0}) : (complexSheafForget X).Faithful :=
  inferInstanceAs (sheafCompose (Opens.grothendieckTopology X) complexModuleForget).Faithful

instance complexSheafForget_preservesFiniteLimits (X : TopCat.{0}) :
    PreservesFiniteLimits (complexSheafForget X) where
  preservesFiniteLimits J _ _ := by
    have : PreservesLimitsOfShape J
        (complexSheafForget X ⋙ TopCat.Sheaf.forget AddCommGrpCat.{0} X) := by
      change PreservesLimitsOfShape J
        (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ) ⋙
          (Functor.whiskeringRight (Opens X)ᵒᵖ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).obj complexModuleForget)
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (complexSheafForget X) (TopCat.Sheaf.forget AddCommGrpCat.{0} X)

instance complexSheafForget_preservesEpimorphisms (X : TopCat.{0}) :
    (complexSheafForget X).PreservesEpimorphisms where
  preserves {F G} f hf := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi ((complexSheafForget X).map f)).mp
    have h := (TopCat.Sheaf.isLocallySurjective_iff_epi f).mpr hf
    constructor
    intro U s
    exact h.imageSieve_mem s

instance complexSheafForget_preservesHomology (X : TopCat.{0}) :
    (complexSheafForget X).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (complexSheafForget X)

instance complexSheafForget_isFlasque {X : TopCat.{0}}
    (F : TopCat.Sheaf (ModuleCat.{0} ℂ) X) [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque ((complexSheafForget X).obj F) where
  epi i := by
    change Epi (complexModuleForget.map (F.obj.map i))
    infer_instance

def complexSheafForgetComplex {X : TopCat.{0}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  ((complexSheafForget X).mapHomologicalComplex (.up ℕ)).obj K

def complexSheafForgetComplexMap {X : TopCat.{0}}
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ} (f : K ⟶ L) :
    complexSheafForgetComplex K ⟶ complexSheafForgetComplex L :=
  ((complexSheafForget X).mapHomologicalComplex (.up ℕ)).map f

def complexSheafForgetHomologyIso {X : TopCat.{0}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ) (n : ℕ) :
    (complexSheafForgetComplex K).homology n ≅ (complexSheafForget X).obj (K.homology n) :=
  (K.sc n).mapHomologyIso (complexSheafForget X)

theorem complexSheafForgetHomologyIso_naturality {X : TopCat.{0}}
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ} (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (complexSheafForgetComplexMap f) n ≫
      (complexSheafForgetHomologyIso L n).hom = (complexSheafForgetHomologyIso K n).hom ≫
        (complexSheafForget X).map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f) (complexSheafForget X)

theorem complexSheafForgetComplex_exactAt_iff {X : TopCat.{0}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ) (n : ℕ) :
    (complexSheafForgetComplex K).ExactAt n ↔ K.ExactAt n :=
  (K.sc n).exact_map_iff_of_faithful (complexSheafForget X)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.SheafForget
