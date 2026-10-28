import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CohomologyComparison
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections
import Mathlib.CategoryTheory.ObjectProperty.Extensions

/-! # Cohomology Finite Coproducts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Actual cohomology, with its original base-ring action, is an additive
module-valued functor. Finiteness is preserved by finite coproducts. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

universe u

def CohomologyFiniteCoproducts.baseCohomologyObject {X B : Scheme.{u}} (f : X ⟶ B) (M : X.Modules) (n : ℕ) :
    ModuleCat.{u} Γ(B, ⊤) :=
  letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M n
  ModuleCat.of Γ(B, ⊤) (SheafCohomology.AffineH.Projective.H M n)

def CohomologyFiniteCoproducts.baseCohomologyMorphism {X B : Scheme.{u}} (f : X ⟶ B) (n : ℕ)
    {M N : X.Modules} (a : M ⟶ N) : CohomologyFiniteCoproducts.baseCohomologyObject f M n ⟶ CohomologyFiniteCoproducts.baseCohomologyObject f N n := by
  letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M n
  letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f N n
  exact ModuleCat.ofHom (CohomologyConnectingScalars.baseCohomologyLinearMap f n a)

def CohomologyFiniteCoproducts.baseCohomologyFunctor {X B : Scheme.{u}} (f : X ⟶ B) (n : ℕ) :
    X.Modules ⥤ ModuleCat.{u} Γ(B, ⊤) where
  obj M := CohomologyFiniteCoproducts.baseCohomologyObject f M n
  map a := CohomologyFiniteCoproducts.baseCohomologyMorphism f n a
  map_id M := by
    apply (forget₂ (ModuleCat Γ(B, ⊤)) AddCommGrpCat).map_injective
    exact (SheafCohomology.AffineH.Projective.zariskiFunctor X n).map_id M
  map_comp a b := by
    apply (forget₂ (ModuleCat Γ(B, ⊤)) AddCommGrpCat).map_injective
    exact (SheafCohomology.AffineH.Projective.zariskiFunctor X n).map_comp a b

instance CohomologyFiniteCoproducts.baseCohomologyFunctor_additive {X B : Scheme.{u}} (f : X ⟶ B) (n : ℕ) :
    (CohomologyFiniteCoproducts.baseCohomologyFunctor f n).Additive where
  map_add := by
    intros M N a b
    apply (forget₂ (ModuleCat Γ(B, ⊤)) AddCommGrpCat).map_injective
    exact (SheafCohomology.AffineH.Projective.zariskiFunctor X n).map_add

theorem CohomologyExactFiniteness.BaseCohomologyFinite.of_isZero {X B : Scheme.{u}} (f : X ⟶ B)
    (M : X.Modules) (h : IsZero M) : CohomologyExactFiniteness.BaseCohomologyFinite f M := by
  intro n
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M n
  have hz := (CohomologyFiniteCoproducts.baseCohomologyFunctor f n).map_isZero h
  have : Subsingleton (SheafCohomology.AffineH.Projective.H M n) := ModuleCat.isZero_iff_subsingleton.mp hz
  infer_instance

instance CohomologyFiniteCoproducts.baseCohomologyFinite_closedUnderIsomorphisms
    {X B : Scheme.{u}} (f : X ⟶ B) :
    ObjectProperty.IsClosedUnderIsomorphisms (CohomologyExactFiniteness.BaseCohomologyFinite f) where
  of_iso e h := h.of_iso f e

instance CohomologyFiniteCoproducts.baseCohomologyFinite_closedUnderExtensions
    {X B : Scheme.{u}} (f : X ⟶ B) [IsNoetherianRing Γ(B, ⊤)] :
    ObjectProperty.IsClosedUnderExtensions (CohomologyExactFiniteness.BaseCohomologyFinite f) where
  prop_X₂_of_shortExact hS h₁ h₃ := CohomologyExactFiniteness.BaseCohomologyFinite.middle f hS h₁ h₃

theorem CohomologyExactFiniteness.BaseCohomologyFinite.coproduct
    {X B : Scheme.{u}} (f : X ⟶ B) {ι : Type} [Fintype ι]
    (M : ι → X.Modules) (h : ∀ i, CohomologyExactFiniteness.BaseCohomologyFinite f (M i)) :
    CohomologyExactFiniteness.BaseCohomologyFinite f (∐ M) := by
  intro n
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f (∐ M) n
  let : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  have (i : ι) : Module.Finite Γ(B, ⊤) ((CohomologyFiniteCoproducts.baseCohomologyFunctor f n).obj (M i)) := h i n
  exact Module.Finite.equiv (SheafCohomology.Projective.AdditiveCoproductSections.additiveCoproductIsoPi (CohomologyFiniteCoproducts.baseCohomologyFunctor f n) M).symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
