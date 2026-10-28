import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCohomology
import OAI.Topology.Euclidean.FilteredCohomology
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Compact Support Colimit -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit

noncomputable section

/-!
# Compact support cohomology as the colimit of relative cohomology

Exactness of filtered colimits of modules identifies the cohomology of the
actual compact-support cochain complex with the filtered colimit of
`H*(X, X \ K; M)`. The comparison uses the actual stage maps. In particular,
every compact-support class comes from one compact support, and its vanishing
is detected after enlarging that compact support.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.Topology.Euclidean.FilteredCohomology.Globalization

variable {R : Type} [Ring R]

/-- Enlargement of support on the actual relative cohomology groups. -/
abbrev compactSupportCohomologyMap (M : ModuleCat.{0} R) {X : TopCat.{0}}
    {K L : Compacts X} (h : K ≤ L) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (K : Set X)ᶜ n ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (L : Set X)ᶜ n :=
  HomologicalComplex.homologyMap (CompactSupportCohomology.compactSupportCochainMap M h) n

@[simp]
theorem compactSupportCohomologyMap_refl (M : ModuleCat.{0} R) (X : TopCat.{0})
    (K : Compacts X) (n : ℕ) : compactSupportCohomologyMap M (le_refl K) n = 𝟙 _ := by
  rw [compactSupportCohomologyMap, CompactSupportCohomology.compactSupportCochainMap_refl,
    HomologicalComplex.homologyMap_id]

@[simp]
theorem compactSupportCohomologyMap_comp (M : ModuleCat.{0} R)
    {X : TopCat.{0}} {K L N : Compacts X} (h : K ≤ L) (h' : L ≤ N) (n : ℕ) :
    compactSupportCohomologyMap M h n ≫ compactSupportCohomologyMap M h' n =
      compactSupportCohomologyMap M (h.trans h') n := by
  rw [← HomologicalComplex.homologyMap_comp, CompactSupportCohomology.compactSupportCochainMap_comp]

@[reassoc (attr := simp)]
theorem compactSupportCohomologyMap_ι (M : ModuleCat.{0} R)
    {X : TopCat.{0}} {K L : Compacts X} (h : K ≤ L) (n : ℕ) :
    compactSupportCohomologyMap M h n ≫ CompactSupportCohomology.compactSupportCohomologyι M X L n =
      CompactSupportCohomology.compactSupportCohomologyι M X K n := by
  rw [← HomologicalComplex.homologyMap_comp, CompactSupportCohomology.compactSupportCochainMap_ι]

/-- The usual direct-limit formulation of compact-support singular cohomology
is canonically isomorphic to the cohomology of the actual colimit complex. -/
def compactSupportCohomologyColimitIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    colimit (CompactSupportCohomology.compactSupportCohomologyDiagram M X n) ≅ CompactSupportCohomology.compactSupportedCohomology M X n :=
  Topology.Euclidean.FilteredCohomology.Globalization.filteredCohomologyComparisonIso (CompactSupportCohomology.compactSupportCochainDiagram M X) n

@[reassoc (attr := simp)]
theorem compactSupportCohomologyColimitIso_ι (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) (K : Compacts X) :
    colimit.ι (CompactSupportCohomology.compactSupportCohomologyDiagram M X n) K ≫
        (compactSupportCohomologyColimitIso M X n).hom =
      CompactSupportCohomology.compactSupportCohomologyι M X K n :=
  Topology.Euclidean.FilteredCohomology.Globalization.filteredCohomologyComparisonIso_ι (CompactSupportCohomology.compactSupportCochainDiagram M X) n K

/-- The actual stage cohomology maps, viewed as a cocone with vertex `Hc`. -/
abbrev compactSupportCohomologyCocone (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    Cocone (CompactSupportCohomology.compactSupportCohomologyDiagram M X n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapCocone
    (colimit.cocone (CompactSupportCohomology.compactSupportCochainDiagram M X))

/-- The genuine compact-support cohomology cocone has the colimit universal property. -/
def compactSupportCohomologyIsColimit (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    IsColimit (compactSupportCohomologyCocone M X n) :=
  isColimitOfPreserves
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n)
    (colimit.isColimit (CompactSupportCohomology.compactSupportCochainDiagram M X))

/-- Compatible maps from relative cohomology on each compact support give a
map from actual compact-support cohomology. -/
def compactSupportedCohomologyDesc (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    {N : ModuleCat.{0} R}
    (f : ∀ K : Compacts X, Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (K : Set X)ᶜ n ⟶ N)
    (hf : ∀ (K L : Compacts X) (h : K ≤ L), compactSupportCohomologyMap M h n ≫ f L = f K) :
    CompactSupportCohomology.compactSupportedCohomology M X n ⟶ N :=
  (compactSupportCohomologyIsColimit M X n).desc {
    pt := N
    ι := {
      app := f
      naturality := fun K L h => by
        change compactSupportCohomologyMap M (leOfHom h) n ≫ f L = f K ≫ 𝟙 N
        rw [Category.comp_id]
        exact hf K L (leOfHom h) } }

@[reassoc (attr := simp)]
theorem compactSupportCohomologyι_desc (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    {N : ModuleCat.{0} R}
    (f : ∀ K : Compacts X, Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (K : Set X)ᶜ n ⟶ N)
    (hf : ∀ (K L : Compacts X) (h : K ≤ L), compactSupportCohomologyMap M h n ≫ f L = f K)
    (K : Compacts X) :
    CompactSupportCohomology.compactSupportCohomologyι M X K n ≫ compactSupportedCohomologyDesc M X n f hf = f K :=
  (compactSupportCohomologyIsColimit M X n).fac _ K

/-- Morphisms from compact-support cohomology are determined on actual compact stages. -/
theorem compactSupportedCohomology_hom_ext (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    {N : ModuleCat.{0} R} {f g : CompactSupportCohomology.compactSupportedCohomology M X n ⟶ N}
    (h : ∀ K, CompactSupportCohomology.compactSupportCohomologyι M X K n ≫ f =
      CompactSupportCohomology.compactSupportCohomologyι M X K n ≫ g) : f = g :=
  (compactSupportCohomologyIsColimit M X n).hom_ext h

/-- Every compact-support cohomology class is represented at one compact support. -/
theorem compactSupportedCohomology_exists_stage (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) (c : CompactSupportCohomology.compactSupportedCohomology M X n) :
    ∃ (K : Compacts X) (a : Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (K : Set X)ᶜ n),
      CompactSupportCohomology.compactSupportCohomologyι M X K n a = c :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (ModuleCat.{0} R))
      (compactSupportCohomologyIsColimit M X n)) c

/-- Two stage classes agree in compact-support cohomology exactly when they
agree after enlargement to a common compact support. -/
theorem compactSupportCohomologyι_eq_iff (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) {K L : Compacts X}
    (a : Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (K : Set X)ᶜ n)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (L : Set X)ᶜ n) :
    CompactSupportCohomology.compactSupportCohomologyι M X K n a = CompactSupportCohomology.compactSupportCohomologyι M X L n b ↔
      ∃ (N : Compacts X) (hK : K ≤ N) (hL : L ≤ N),
        compactSupportCohomologyMap M hK n a = compactSupportCohomologyMap M hL n b := by
  have heq := Types.FilteredColimit.isColimit_eq_iff
    (CompactSupportCohomology.compactSupportCohomologyDiagram M X n ⋙ forget (ModuleCat.{0} R))
    (isColimitOfPreserves (forget (ModuleCat.{0} R))
      (compactSupportCohomologyIsColimit M X n)) (xi := a) (xj := b)
  constructor
  · intro h
    obtain ⟨N, f, g, hab⟩ := heq.mp h
    exact ⟨N, leOfHom f, leOfHom g, hab⟩
  · rintro ⟨N, hK, hL, hab⟩
    exact heq.mpr ⟨N, homOfLE hK, homOfLE hL, hab⟩

/-- A stage class vanishes in compact-support cohomology exactly when it
vanishes at some larger actual compact support. -/
theorem compactSupportCohomologyι_eq_zero_iff (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) {K : Compacts X}
    (a : Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (K : Set X)ᶜ n) :
    CompactSupportCohomology.compactSupportCohomologyι M X K n a = 0 ↔
      ∃ (N : Compacts X) (h : K ≤ N), compactSupportCohomologyMap M h n a = 0 := by
  constructor
  · intro h
    have h' : CompactSupportCohomology.compactSupportCohomologyι M X K n a =
        CompactSupportCohomology.compactSupportCohomologyι M X K n 0 := by simpa using h
    obtain ⟨N, hK, hK', ha⟩ := (compactSupportCohomologyι_eq_iff M X n a 0).mp h'
    exact ⟨N, hK, by simpa using ha⟩
  · rintro ⟨N, hK, ha⟩
    have h' := (compactSupportCohomologyι_eq_iff M X n a 0).mpr
      ⟨N, hK, hK, by simpa using ha⟩
    simpa using h'

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit
