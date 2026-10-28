import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.Flasque

/-! # Homeomorph Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HomeomorphSheaf.HomeomorphSheafTransport

noncomputable section

/-! Sheaf and Cech transport along a homeomorphism between arbitrary universes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u v a b w
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y)

def opens : Opens X ⥤ Opens Y := h.opensCongr.equivalence.functor

instance opens_isEquivalence : (opens h).IsEquivalence := by
  dsimp only [opens]
  infer_instance

theorem coverPreserving : CoverPreserving (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y) (opens h) := by
  constructor
  intro U S hS y hy
  change h.symm y ∈ U at hy
  obtain ⟨V, i, hi, hx⟩ := hS (h.symm y) hy
  exact ⟨_, (opens h).map i, ⟨_, i, 𝟙 _, hi, Subsingleton.elim _ _⟩, hx⟩

instance opens_isContinuous : (opens h).IsContinuous
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _) (coverPreserving h)

variable (A : Type a) [Category.{b} A]

def transport : Sheaf (Opens.grothendieckTopology X) A ⥤ Sheaf (Opens.grothendieckTopology Y) A :=
  (opens h.symm).sheafPushforwardContinuous A _ _

instance transport_flasque (F : Sheaf (Opens.grothendieckTopology X) A)
    [hF : TopCat.Presheaf.IsFlasque (X := TopCat.of X) F.obj] :
    TopCat.Presheaf.IsFlasque (X := TopCat.of Y) (((transport h A).obj F).obj) where
  epi i := by
    change Epi (F.obj.map ((opens h.symm).op.map i))
    exact hF.epi _

variable [Preadditive A] [HasProducts.{w} A] {ι : Type w} (U : ι → Opens Y)
  (F : Sheaf (Opens.grothendieckTopology X) A)

def cechIso :
    (cechComplexFunctor U).obj ((transport h A).obj F).obj ≅
      (cechComplexFunctor ((opens h.symm).obj ∘ U)).obj F.obj :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (opens h.symm) U F.obj

theorem cover (hU : iSup U = ⊤) : iSup ((opens h.symm).obj ∘ U) = ⊤ := by
  change (⨆ i, h.symm.opensCongr (U i)) = ⊤
  rw [← OrderIso.map_iSup, hU, OrderIso.map_top]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HomeomorphSheaf.HomeomorphSheafTransport
