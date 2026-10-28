import OAI.AlgebraicTopology.DeRham.Comparison.RationalSheafForget
import OAI.AlgebraicGeometry.CycleClass.Geometric.FlasqueLowDegree

/-! # Rational Flasque Low Degree -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree

noncomputable section

/-!
# Low-degree global cohomology of rational flasque sheaf complexes

The additive-group theorem is transported through the actual exact rational
forgetful functor and its proved section and homology comparisons. The final
isomorphisms are rational-linear: fullness of the ordinary forgetful functor
comes from automatic rational linearity of additive maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : TopCat.{u}}

/-- The additive-group comparison is assembled only from the proved exact
forgetful functor, actual section comparisons, and the flasque edge theorem. -/
def rationalFlasqueLowDegreeForgetIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) (n : ℕ) (hn : n ≤ d) :
    RationalSheafForget.rationalForget.obj ((RationalSheafForget.rationalSheafSectionsComplex (⊤ : Opens X) K).homology n) ≅
      RationalSheafForget.rationalForget.obj ((RationalSheafForget.rationalSheafSections (⊤ : Opens X)).obj (K.homology n)) := by
  have hKA : ∀ j, TopCat.Sheaf.IsFlasque ((RationalSheafForget.rationalSheafForgetComplex K).X j) := by
    intro j
    have := hK j
    change TopCat.Sheaf.IsFlasque ((RationalSheafForget.rationalSheafForget X).obj (K.X j))
    infer_instance
  have heA : ∀ j, j < d → (RationalSheafForget.rationalSheafForgetComplex K).ExactAt j := by
    intro j hj
    exact (RationalSheafForget.rationalSheafForgetComplex_exactAt_iff K j).mpr (he j hj)
  exact RationalSheafForget.rationalSectionsForgetHomologyIso ⊤ K n ≪≫
    AlgebraicGeometry.CycleClass.Geometric.FlasqueLowDegree.Cycles.flasqueLowDegreeHomologyIso
      (RationalSheafForget.rationalSheafForgetComplex K) hKA d heA n hn ≪≫
    (AlgebraicGeometry.CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapIso (RationalSheafForget.rationalSheafForgetHomologyIso K n) ≪≫
    (RationalSheafForget.rationalSheafForgetSectionsIso (⊤ : Opens X)).app (K.homology n)

/-- In every degree through the first potentially nonzero cohomology sheaf,
global rational cohomology equals the sections of that cohomology sheaf. -/
def rationalFlasqueLowDegreeHomologyIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) (n : ℕ) (hn : n ≤ d) :
    (RationalSheafForget.rationalSheafSectionsComplex (⊤ : Opens X) K).homology n ≅
      (RationalSheafForget.rationalSheafSections (⊤ : Opens X)).obj (K.homology n) :=
  RationalSheafForget.rationalForget.preimageIso (rationalFlasqueLowDegreeForgetIso K hK d he n hn)

/-- Forgetting the constructed rational isomorphism recovers exactly the
proved additive comparison; no new comparison map is postulated. -/
theorem rationalFlasqueLowDegreeHomologyIso_map
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) (n : ℕ) (hn : n ≤ d) :
    RationalSheafForget.rationalForget.mapIso (rationalFlasqueLowDegreeHomologyIso K hK d he n hn) =
      rationalFlasqueLowDegreeForgetIso K hK d he n hn := by
  apply Iso.ext
  exact RationalSheafForget.rationalForget.map_preimage _

/-- Below the first nonzero cohomology sheaf, the genuine global rational
section complex is exact. -/
theorem rationalFlasqueLowDegree_exactAt
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) (n : ℕ) (hn : n < d) :
    (RationalSheafForget.rationalSheafSectionsComplex (⊤ : Opens X) K).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((RationalSheafForget.rationalSheafSections (⊤ : Opens X)).map_isZero
    (he n hn).isZero_homology).of_iso
      (rationalFlasqueLowDegreeHomologyIso K hK d he n hn.le)

/-- The rational-linear edge isomorphism in the first potentially nonzero
degree of a bounded-below flasque sheaf complex. -/
def rationalFlasqueFirstCohomologyIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u,0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (d : ℕ) (he : ∀ n, n < d → K.ExactAt n) :
    (RationalSheafForget.rationalSheafSectionsComplex (⊤ : Opens X) K).homology d ≅
      (RationalSheafForget.rationalSheafSections (⊤ : Opens X)).obj (K.homology d) :=
  rationalFlasqueLowDegreeHomologyIso K hK d he d le_rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree
