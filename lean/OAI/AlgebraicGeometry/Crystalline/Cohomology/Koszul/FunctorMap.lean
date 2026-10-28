import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Functor Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.FunctorMap.KoszulFunctorMap

noncomputable section

/-! # Natural coefficient maps induce maps of the actual tensor coordinate complexes -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u v w

variable (R σ : Type u) [CommRing R] [Fintype σ]
  {C : Type v} [Category.{w} C] {F G : C ⥤ ModuleCat.{u} R}
  (D : σ → (F ⟶ F)) (E : σ → (G ⟶ G))
  (hD : ∀ t i j, Function.Commute (Functor.KoszulFunctor.derivatives R σ F D t i)
    (Functor.KoszulFunctor.derivatives R σ F D t j))
  (hE : ∀ t i j, Function.Commute (Functor.KoszulFunctor.derivatives R σ G E t i)
    (Functor.KoszulFunctor.derivatives R σ G E t j))
  (α : F ⟶ G) (hα : ∀ t i x, (α.app t).hom (Functor.KoszulFunctor.derivatives R σ F D t i x) =
    Functor.KoszulFunctor.derivatives R σ G E t i ((α.app t).hom x))

def object (t : C) : Functor.KoszulFunctor.object R σ F D hD t ⟶ Functor.KoszulFunctor.object R σ G E hE t :=
  TensorMap.KoszulTensorMap.map R σ (F.obj t) (G.obj t) (Functor.KoszulFunctor.derivatives R σ F D t)
    (Functor.KoszulFunctor.derivatives R σ G E t) (α.app t).hom (hα t) (hD t) (hE t)

def raw : Functor.KoszulFunctor.functor R σ F D hD ⟶ Functor.KoszulFunctor.functor R σ G E hE where
  app := object R σ D E hD hE α hα
  naturality {t s} f := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro ω
    change (α.app s).hom ((F.map f).hom x) ⊗ₜ[R] ω = (G.map f).hom ((α.app t).hom x) ⊗ₜ[R] ω
    exact congrArg (fun y : G.obj s => y ⊗ₜ[R] ω)
      (congrArg (fun g : F.obj t ⟶ G.obj s => g.hom x) (α.naturality f))

def map : Functor.KoszulFunctor.complex R σ F D hD ⟶ Functor.KoszulFunctor.complex R σ G E hE :=
  ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (raw R σ D E hD hE α hα)

theorem map_component (n : ℕ) (t : C) (x : F.obj t) (ω : ⋀[R]^n (σ →₀ R)) :
    (((KoszulFunctorMap.map R σ D E hD hE α hα).f n).app t).hom (x ⊗ₜ[R] ω) = (α.app t).hom x ⊗ₜ[R] ω := rfl

variable [IsIso α]

instance object_isIso (t : C) : IsIso (object R σ D E hD hE α hα t) := by
  have hc : ∀ n, IsIso ((object R σ D E hD hE α hα t).f n) := by
    intro n
    let e := TensorProduct.congr (asIso (α.app t)).toLinearEquiv (LinearEquiv.refl R (⋀[R]^n (σ →₀ R)))
    exact (ConcreteCategory.isIso_iff_bijective _).2 e.bijective
  let := hc
  exact HomologicalComplex.Hom.isIso_of_components _

instance raw_isIso : IsIso (raw R σ D E hD hE α hα) := by
  have hc : ∀ t, IsIso ((raw R σ D E hD hE α hα).app t) :=
    fun t => object_isIso R σ D E hD hE α hα t
  let := hc
  exact NatIso.isIso_of_isIso_app _

instance map_isIso : IsIso (KoszulFunctorMap.map R σ D E hD hE α hα) :=
  inferInstanceAs (IsIso ((ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).map (raw R σ D E hD hE α hα)))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.FunctorMap.KoszulFunctorMap
