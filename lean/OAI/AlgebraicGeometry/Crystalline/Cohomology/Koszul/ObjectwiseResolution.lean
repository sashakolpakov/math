import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ConstantsRetraction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SingleComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Objectwise Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ObjectwiseResolution.KoszulObjectwiseResolution

noncomputable section

/-!
# A resolution from objectwise coordinate primitives

If natural commuting coordinate operators have objectwise commuting
primitives and their final constant projection splits through coefficients,
the resulting tensor complex resolves that actual coefficient functor.
The canonical augmentation is a quasi-isomorphism in the functor category.
The chosen primitives and coefficient retractions need not be natural;
only the coefficient inclusion and derivatives enter the natural chain map.
-/

open _root_.CategoryTheory
open scoped TensorProduct

universe u v w

variable (R σ : Type u) [CommRing R] [Fintype σ]
  {C : Type v} [Category.{w} C] (F G : C ⥤ ModuleCat.{u} R)
  (D : σ → (F ⟶ F)) (S : ∀ t : C, σ → Module.End R (F.obj t))

local notation "d" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor.KoszulFunctor.derivatives R σ F D
local notation "s" => S

variable (hD : ∀ (t : C) (i j : σ),
    Function.Commute (Functor.KoszulFunctor.derivatives R σ F D t i) (Functor.KoszulFunctor.derivatives R σ F D t j))
  (hright : ∀ (t : C) (i : σ) (a : F.obj t),
    Functor.KoszulFunctor.derivatives R σ F D t i (S t i a) = a)
  (hcommS : ∀ (t : C) (i j : σ), j ≠ i → ∀ a : F.obj t,
    Functor.KoszulFunctor.derivatives R σ F D t j (S t i a) =
      S t i (Functor.KoszulFunctor.derivatives R σ F D t j a))
  (l : List σ) (hl : ∀ i, i ∈ l) (c : G ⟶ F) (r : ∀ t : C, F.obj t →ₗ[R] G.obj t)
  (hrc : ∀ t, (r t).comp (c.app t).hom = LinearMap.id)
  (hc : ∀ (t : C) (i : σ) (a : G.obj t), Functor.KoszulFunctor.derivatives R σ F D t i ((c.app t).hom a) = 0)
  (hprojection : ∀ t, SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ (F.obj t)
    (Functor.KoszulFunctor.derivatives R σ F D t) (S t) l =
    (c.app t).hom.comp (r t))

local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor.KoszulFunctor.functor R σ F D hD

def homotopyEquiv (t : C) : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat R)).obj (G.obj t)) ((K).obj t) :=
  ConstantsRetraction.KoszulConstantsRetraction.homotopyEquiv R σ (F.obj t) (G.obj t) (d t) (s t) (hD t)
    (hright t) (hcommS t) l hl (c.app t).hom (r t) (hrc t) (hc t) (hprojection t)

local notation "H" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ObjectwiseResolution.KoszulObjectwiseResolution.homotopyEquiv R σ F G D S hD hright hcommS l hl c r hrc hc hprojection

theorem augmentation_zero (t : C) : ((H t).hom).f 0 =
    ModuleCat.ofHom (ConstantsRetraction.KoszulConstantsRetraction.inclusionZero R σ (F.obj t) (G.obj t) (c.app t).hom) :=
  SingleRetraction.SingleRetractionHomotopy.augmentation_zero _ _ _ _

def rawAugmentation : G ⋙ CochainComplex.single₀ (ModuleCat R) ⟶ K where
  app t := (H t).hom
  naturality {t z} f := by
    apply HomologicalComplex.from_single_hom_ext
    change ((CochainComplex.single₀ (ModuleCat R)).map (G.map f)).f 0 ≫ ((H z).hom).f 0 =
      ((H t).hom).f 0 ≫ ((K).map f).f 0
    rw [augmentation_zero, augmentation_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (TensorDegree.TensorDegreeZero.equiv R σ (F.obj z)).symm ((c.app z).hom ((G.map f).hom a)) =
      TensorProduct.map (F.map f).hom LinearMap.id
        ((TensorDegree.TensorDegreeZero.equiv R σ (F.obj t)).symm ((c.app t).hom a))
    rw [TensorDegree.TensorDegreeZero.equiv_symm, TensorDegree.TensorDegreeZero.equiv_symm, TensorProduct.map_tmul, LinearMap.id_apply]
    exact congrArg (fun b : F.obj z => b ⊗ₜ[R] (exteriorPower.zeroEquiv R (σ →₀ R)).symm 1)
      (congrArg (fun g : G.obj t ⟶ F.obj z => g.hom a) (c.naturality f))

def augmentation : (CochainComplex.single₀ (C ⥤ ModuleCat R)).obj G ⟶
    Functor.KoszulFunctor.complex R σ F D hD :=
  (SingleComplex.SingleComplexAssembly.iso G).inv ≫ ComplexAssemblyQuasi.ComplexAssembly.map (ComplexShape.up ℕ)
    (rawAugmentation R σ F G D S hD hright hcommS l hl c r hrc hc hprojection)

instance augmentation_quasiIso : QuasiIso (augmentation R σ F G D S hD hright hcommS l hl c r hrc hc hprojection) := by
  have hraw : QuasiIso (ComplexAssemblyQuasi.ComplexAssembly.map (ComplexShape.up ℕ)
      (rawAugmentation R σ F G D S hD hright hcommS l hl c r hrc hc hprojection)) :=
    ComplexAssemblyQuasi.ComplexAssembly.map_quasiIso (ComplexShape.up ℕ) _ (fun t => HomotopyEquiv.quasiIso_hom (H t))
  exact quasiIso_comp (SingleComplex.SingleComplexAssembly.iso G).inv
    (ComplexAssemblyQuasi.ComplexAssembly.map (ComplexShape.up ℕ)
      (rawAugmentation R σ F G D S hD hright hcommS l hl c r hrc hc hprojection))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ObjectwiseResolution.KoszulObjectwiseResolution
