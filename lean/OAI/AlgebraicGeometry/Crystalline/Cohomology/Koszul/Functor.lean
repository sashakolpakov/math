import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi

/-! # Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor.KoszulFunctor

noncomputable section

/-!
# Functorial tensor coordinate complexes

Commuting natural endomorphisms of a module-valued functor give a
functor of actual tensor coordinate complexes, and hence a complex
in the functor category. Every coefficient morphism induces the
corresponding tensor chain map.
-/

open _root_.CategoryTheory
open scoped TensorProduct

universe u v w

variable (R σ : Type u) [CommRing R] [Fintype σ]
  {C : Type v} [Category.{w} C] (F : C ⥤ ModuleCat.{u} R)
  (D : σ → (F ⟶ F))

def derivatives (t : C) (i : σ) : Module.End R (F.obj t) := ((D i).app t).hom

variable (hD : ∀ t i j, Function.Commute (derivatives R σ F D t i) (derivatives R σ F D t j))

def object (t : C) : CochainComplex (ModuleCat R) ℕ :=
  Tensor.KoszulTensor.complex R σ (F.obj t) (derivatives R σ F D t) (hD t)

omit [Fintype σ] in
theorem derivative_naturality {t s : C} (f : t ⟶ s) (i : σ) (a : F.obj t) :
    (F.map f).hom (derivatives R σ F D t i a) = derivatives R σ F D s i ((F.map f).hom a) := by
  have h := congrArg (fun g : F.obj t ⟶ F.obj s => g.hom a) ((D i).naturality f)
  exact h.symm

def map {t s : C} (f : t ⟶ s) : object R σ F D hD t ⟶ object R σ F D hD s :=
  TensorMap.KoszulTensorMap.map R σ (F.obj t) (F.obj s) (derivatives R σ F D t) (derivatives R σ F D s)
    (F.map f).hom (derivative_naturality R σ F D f) (hD t) (hD s)

theorem map_id (t : C) : KoszulFunctor.map R σ F D hD (𝟙 t) = 𝟙 (object R σ F D hD t) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro ω
  change (F.map (𝟙 t)).hom a ⊗ₜ[R] ω = a ⊗ₜ[R] ω
  rw [F.map_id]
  rfl

theorem map_comp {t s z : C} (f : t ⟶ s) (g : s ⟶ z) :
    KoszulFunctor.map R σ F D hD (f ≫ g) = KoszulFunctor.map R σ F D hD f ≫ KoszulFunctor.map R σ F D hD g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro ω
  change (F.map (f ≫ g)).hom a ⊗ₜ[R] ω = (F.map g).hom ((F.map f).hom a) ⊗ₜ[R] ω
  rw [F.map_comp]
  rfl

def functor : C ⥤ CochainComplex (ModuleCat R) ℕ where
  obj := object R σ F D hD
  map := KoszulFunctor.map R σ F D hD
  map_id := KoszulFunctor.map_id R σ F D hD
  map_comp := KoszulFunctor.map_comp R σ F D hD

/-- The assembled coordinate complex in the actual functor category. -/
def complex : CochainComplex (C ⥤ ModuleCat R) ℕ :=
  ComplexAssemblyQuasi.ComplexAssembly.complex (ComplexShape.up ℕ) (functor R σ F D hD)

def evaluationIso (t : C) :
    (((evaluation C (ModuleCat R)).obj t).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (complex R σ F D hD) ≅ object R σ F D hD t :=
  ComplexAssemblyQuasi.ComplexAssembly.evaluationIso (ComplexShape.up ℕ) (functor R σ F D hD) t

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor.KoszulFunctor
