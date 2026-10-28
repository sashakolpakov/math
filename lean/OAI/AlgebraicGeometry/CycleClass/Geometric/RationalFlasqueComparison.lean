import OAI.AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree
import OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition

/-! # Rational Flasque Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RationalFlasqueComparison

noncomputable section

/-!
# The map underlying the rational flasque comparison

The rational flasque isomorphism was constructed by forgetting scalars,
applying the actual additive flasque comparison, and using fullness to lift
back to rational modules. Its forward map is the canonical left-exact
homology comparison. Faithfulness of the forgetful functor reduces the proof
to composition of the existing comparison maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

open OAI.AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition

variable {X : TopCat.{0}}

/-- Rational sections preserve finite limits because both the underlying
presheaf functor and evaluation preserve them. -/
instance rationalSheafSections_preservesFiniteLimits (U : Opens X) :
    PreservesFiniteLimits (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSections U) := by
  have : PreservesFiniteLimits (TopCat.Sheaf.forget (ModuleCat ℚ) X) := inferInstance
  have : PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ (ModuleCat ℚ)).obj (op U)) := inferInstance
  exact comp_preservesFiniteLimits (TopCat.Sheaf.forget (ModuleCat ℚ) X)
    ((evaluation (Opens X)ᵒᵖ (ModuleCat ℚ)).obj (op U))

/-- The additive flasque isomorphism uses exactly the canonical left-exact
comparison, once its required individual cokernel preservation is proved. -/
theorem flasqueLowDegreeHomologyIso_hom_eq_leftExactHomologyComparison
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℕ)
    (hK : ∀ j, TopCat.Sheaf.IsFlasque (K.X j))
    (d : ℕ) (he : ∀ j, j < d → K.ExactAt j) (n : ℕ) (hn : n ≤ d) :
    (FlasqueLowDegree.Cycles.flasqueLowDegreeHomologyIso K hK d he n hn).hom =
      AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison (K.sc n) (FlasqueLowDegree.Cycles.sheafGlobalSections X) := by
  have := FlasqueLowDegree.Cycles.globalSections_preservesRightHomologyOf K hK d he n hn
  exact (AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso.leftExactHomologyComparison_eq_mapHomologyIso' (K.sc n)
    (FlasqueLowDegree.Cycles.sheafGlobalSections X)).symm

private theorem rationalSheafForgetSectionsComplexIso_inv_eq_id (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat ℚ) X) ℕ) :
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetSectionsComplexIso U K).inv = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  rfl

private theorem rationalSectionsForgetHomologyIso_hom_eq (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat ℚ) X) ℕ) (n : ℕ) :
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSectionsForgetHomologyIso U K n).hom =
      (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSectionsComplex U K) n).inv := by
  dsimp only [AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSectionsForgetHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  rw [rationalSheafForgetSectionsComplexIso_inv_eq_id]
  change (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSectionsComplex U K) n).inv ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n).map
      (𝟙 ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSectionsComplex U K))) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

private theorem rationalSheafForgetHomologyIso_hom_eq
    (K : CochainComplex (TopCat.Sheaf (ModuleCat ℚ) X) ℕ) (n : ℕ) :
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetHomologyIso K n).hom =
      AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison (K.sc n) (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X) := by
  rw [AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso.leftExactHomologyComparison_eq_mapHomologyIso',
    ShortComplex.mapHomologyIso'_eq_mapHomologyIso]
  rfl

/-- The constructed rational-linear flasque comparison has the canonical
left-exact homology comparison as its actual forward map. -/
theorem rationalFlasqueLowDegreeHomologyIso_hom_eq_leftExactHomologyComparison
    (K : CochainComplex (TopCat.Sheaf (ModuleCat ℚ) X) ℕ)
    (hK : ∀ j, TopCat.Sheaf.IsFlasque (K.X j))
    (d : ℕ) (he : ∀ j, j < d → K.ExactAt j) (n : ℕ) (hn : n ≤ d) :
    (AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree.rationalFlasqueLowDegreeHomologyIso K hK d he n hn).hom =
      AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison (K.sc n) (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSections (⊤ : Opens X)) := by
  have hKA : ∀ j, TopCat.Sheaf.IsFlasque ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex K).X j) := by
    intro j
    have := hK j
    change TopCat.Sheaf.IsFlasque ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X).obj (K.X j))
    infer_instance
  have heA : ∀ j, j < d → (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex K).ExactAt j := by
    intro j hj
    exact (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex_exactAt_iff K j).mpr (he j hj)
  have hlast : ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetSectionsIso (⊤ : Opens X)).app (K.homology n)).hom =
      𝟙 _ := rfl
  have hformula : (AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree.rationalFlasqueLowDegreeForgetIso K hK d he n hn).hom =
      (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSectionsComplex ⊤ K) n).inv ≫
        (FlasqueLowDegree.Cycles.flasqueLowDegreeHomologyIso (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex K) hKA d heA n hn).hom ≫
          (FlasqueLowDegree.Cycles.sheafGlobalSections X).map (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetHomologyIso K n).hom := by
    dsimp only [AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree.rationalFlasqueLowDegreeForgetIso, Iso.trans_hom, Functor.mapIso_hom]
    rw [rationalSectionsForgetHomologyIso_hom_eq, hlast]
    rfl
  apply AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map_injective
  have hmap := congrArg Iso.hom (AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree.rationalFlasqueLowDegreeHomologyIso_map K hK d he n hn)
  change AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map (AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree.rationalFlasqueLowDegreeHomologyIso K hK d he n hn).hom =
    (AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree.rationalFlasqueLowDegreeForgetIso K hK d he n hn).hom at hmap
  rw [hmap, hformula]
  apply (cancel_epi
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSectionsComplex ⊤ K) n).hom).mp
  rw [Iso.hom_inv_id_assoc,
    flasqueLowDegreeHomologyIso_hom_eq_leftExactHomologyComparison,
    rationalSheafForgetHomologyIso_hom_eq]
  change AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison ((K.sc n).map (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X))
      (FlasqueLowDegree.Cycles.sheafGlobalSections X) ≫
        (FlasqueLowDegree.Cycles.sheafGlobalSections X).map
          (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison (K.sc n) (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X)) =
    (((K.sc n).map (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSections (⊤ : Opens X))).mapHomologyIso AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget).hom ≫
      AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map
        (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison (K.sc n) (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSections (⊤ : Opens X)))
  rw [← AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition.leftExactHomologyComparison_eq_mapHomologyIso,
    AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition.leftExactHomologyComparison_comp, AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition.leftExactHomologyComparison_comp]
  rfl

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RationalFlasqueComparison
