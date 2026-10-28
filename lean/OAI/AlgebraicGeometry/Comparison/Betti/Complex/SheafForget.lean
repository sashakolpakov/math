import OAI.AlgebraicTopology.DeRham.Comparison.RationalSheafForget
import Mathlib.Basic.Complex.Basic

/-! # Sheaf Forget -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafForget.Flasque

noncomputable section

/-!
# Exact forgetting of complex scalars on actual sheaves

Literal postcomposition with the module forgetful functor preserves exactness
and detects flasqueness. This transfers the proved abelian-group sheaf-gluing
theorems to complex coefficients without changing section groups or maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

abbrev scalarForget : ModuleCat.{0} ℂ ⥤ AddCommGrpCat.{0} :=
  forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}

def sheafForget (X : TopCat.{0}) :
    TopCat.Sheaf (ModuleCat.{0} ℂ) X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
  sheafCompose (Opens.grothendieckTopology X) scalarForget

instance sheafForgetAdditive (X : TopCat.{0}) : (sheafForget X).Additive where
  map_add := rfl

instance sheafForgetFaithful (X : TopCat.{0}) : (sheafForget X).Faithful :=
  inferInstanceAs (sheafCompose (Opens.grothendieckTopology X) scalarForget).Faithful

instance sheafForgetPreservesFiniteLimits (X : TopCat.{0}) :
    PreservesFiniteLimits (sheafForget X) where
  preservesFiniteLimits J _ _ := by
    have : PreservesLimitsOfShape J (sheafForget X ⋙ TopCat.Sheaf.forget AddCommGrpCat.{0} X) := by
      change PreservesLimitsOfShape J
        (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ) ⋙
          (Functor.whiskeringRight (Opens X)ᵒᵖ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).obj scalarForget)
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (sheafForget X) (TopCat.Sheaf.forget AddCommGrpCat.{0} X)

instance sheafForgetPreservesEpimorphisms (X : TopCat.{0}) :
    (sheafForget X).PreservesEpimorphisms where
  preserves {F G} f hf := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi ((sheafForget X).map f)).mp
    have h := (TopCat.Sheaf.isLocallySurjective_iff_epi f).mpr hf
    constructor
    intro U s
    exact h.imageSieve_mem s

instance sheafForgetPreservesHomology (X : TopCat.{0}) : (sheafForget X).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (sheafForget X)

instance sheafForgetFlasque {X : TopCat.{0}}
    (F : TopCat.Sheaf (ModuleCat.{0} ℂ) X) [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque ((sheafForget X).obj F) where
  epi i := by
    change Epi (scalarForget.map (F.obj.map i))
    infer_instance

theorem flasque_of_sheafForget {X : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℂ) X)
    [TopCat.Sheaf.IsFlasque ((sheafForget X).obj F)] : TopCat.Sheaf.IsFlasque F where
  epi i := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact (AddCommGrpCat.epi_iff_surjective (((sheafForget X).obj F).obj.map i)).mp inferInstance

theorem sheafForget_shortExact {X : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X)) (hS : S.ShortExact) :
    (S.map (sheafForget X)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map (sheafForget X)

/-- Actual open-section surjectivity for a short exact sequence with flasque kernel. -/
theorem flasque_section_epi {X : TopCat.{0}} (U : Opens X)
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X))
    (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁] : Epi (S.g.hom.app (op U)) := by
  have hSA := sheafForget_shortExact S hS
  have : TopCat.Sheaf.IsFlasque (S.map (sheafForget X)).X₁ := sheafForgetFlasque S.X₁
  have he : Epi ((S.map (sheafForget X)).g.hom.app (op U)) :=
    TopCat.Sheaf.IsFlasque.epi_of_shortExact hSA
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact (AddCommGrpCat.epi_iff_surjective _).mp he

theorem flasque_of_shortExact₁₂ {X : TopCat.{0}}
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X)) (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque S.X₁] [TopCat.Sheaf.IsFlasque S.X₂] : TopCat.Sheaf.IsFlasque S.X₃ := by
  have : TopCat.Sheaf.IsFlasque (S.map (sheafForget X)).X₁ := sheafForgetFlasque S.X₁
  have : TopCat.Sheaf.IsFlasque (S.map (sheafForget X)).X₂ := sheafForgetFlasque S.X₂
  have : TopCat.Sheaf.IsFlasque ((sheafForget X).obj S.X₃) :=
    TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ (sheafForget_shortExact S hS)
  exact flasque_of_sheafForget S.X₃

end

end OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafForget.Flasque
