import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Linear
import Mathlib.RingTheory.Regular.Category
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Quotient Complex -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuotientComplex

noncomputable section

/-! Reduction of an actual chain complex modulo a regular parameter
gives a short exact sequence of complexes and its native homology
connecting maps. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Pointwise

universe u

variable (R : Type u) [CommRing R] (r : R)

def quotient : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := .of R (QuotSMulTop r M)
  map f := ModuleCat.ofHom (QuotSMulTop.map r f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    exact QuotSMulTop.map_id r M
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact QuotSMulTop.map_comp r g.hom f.hom

instance : (quotient R r).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    exact (QuotSMulTop.map r).map_add f.hom g.hom

variable (K : ChainComplex (ModuleCat.{u} R) ℕ)

def complex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((quotient R r).mapHomologicalComplex (ComplexShape.down ℕ)).obj K

def projection : K ⟶ complex R r K where
  f i := ModuleCat.ofHom (r • (⊤ : Submodule R (K.X i))).mkQ
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

theorem scalar_projection : (r • 𝟙 K) ≫ projection R r K = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (Submodule.Quotient.mk (r • x) : QuotSMulTop r (K.X i)) = 0
  exact (Submodule.Quotient.mk_eq_zero (r • (⊤ : Submodule R (K.X i)))).mpr
    (Submodule.smul_mem_pointwise_smul x r ⊤ trivial)

def sequence : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (r • 𝟙 K) (projection R r K) (scalar_projection R r K)

theorem shortExact (hr : ∀ i, IsSMulRegular (K.X i) r) : (sequence R r K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact IsSMulRegular.smulShortComplex_shortExact (hr i)

theorem homology_scalar (i : ℕ) :
    HomologicalComplex.homologyMap (sequence R r K).f i = r • 𝟙 (K.homology i) := by
  change (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) i).map (r • 𝟙 K) = _
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

def connecting (hr : ∀ i, IsSMulRegular (K.X i) r) (i : ℕ) :
    (complex R r K).homology (i + 1) ⟶ K.homology i :=
  (shortExact R r K hr).δ (i + 1) i (by simp)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuotientComplex
