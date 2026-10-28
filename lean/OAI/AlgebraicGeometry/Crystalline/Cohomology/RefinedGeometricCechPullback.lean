import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.OpenBaseChangeNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyRefinement
import Mathlib.CategoryTheory.Limits.Preserves.Lattice

/-! # Refined Geometric Cech Pullback -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback

noncomputable section

/-! Actual refined geometric pullback of direct Cech cochains, with its coefficient squares and intersection projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u

abbrev Presheaves (R : Type u) [CommRing R] (X : Scheme.{u}) := X.Opensᵒᵖ ⥤ ModuleCat.{u} R

section Foundations
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
def preimage : Y.Opens ⥤ X.Opens := TopologicalSpace.Opens.map f.base
instance preimage_preservesFiniteLimits : PreservesFiniteLimits (preimage f) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.base.frameHom).toFunctor
  infer_instance
def functor : Presheaves R X ⥤ Presheaves R Y :=
  (Functor.whiskeringLeft _ _ _).obj (preimage f).op
instance functor_additive : (functor R f).Additive := by
  unfold functor
  infer_instance
end Foundations

section Covers
variable (X : Scheme.{u}) {ι κ : Type} (U : ι → X.Opens) (V : κ → X.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ U (r i))
def coverMap : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U where
  f := r
  φ i := homOfLE (hr i)
end Covers

private theorem three_squares {C : Type*} [Category* C] {A B D E A' B' D' E' : C}
    (e₁ : A ⟶ B) (e₂ : B ⟶ D) (e₃ : D ⟶ E)
    (f₁ : A' ⟶ B') (f₂ : B' ⟶ D') (f₃ : D' ⟶ E')
    (a : A ⟶ A') (b : B ⟶ B') (c : D ⟶ D') (d : E ⟶ E')
    (h₁ : a ≫ f₁ = e₁ ≫ b) (h₂ : b ≫ f₂ = e₂ ≫ c) (h₃ : c ≫ f₃ = e₃ ≫ d) :
    a ≫ (f₁ ≫ f₂ ≫ f₃) = (e₁ ≫ e₂ ≫ e₃) ≫ d := by
  calc
    a ≫ (f₁ ≫ f₂ ≫ f₃) = e₁ ≫ (b ≫ f₂) ≫ f₃ := by
      rw [← Category.assoc a f₁ (f₂ ≫ f₃), h₁]
      simp only [Category.assoc]
    _ = e₁ ≫ (e₂ ≫ c) ≫ f₃ := by rw [h₂]
    _ = (e₁ ≫ e₂) ≫ (c ≫ f₃) := by simp only [Category.assoc]
    _ = (e₁ ≫ e₂ ≫ e₃) ≫ d := by rw [h₃]; simp only [Category.assoc]

section Maps
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.Opens) (V : κ → X.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f ⁻¹ᵁ U (r i))

def map {P : Presheaves R Y} {Q : Presheaves R X}
    (b : P ⟶ (functor R f).obj Q) :
    (cechComplexFunctor U).obj P ⟶ (cechComplexFunctor V).obj Q :=
  (cechComplexFunctor U).map b ≫ (Cech.BaseChange.CechBaseChange.complexIso (preimage f) U Q).hom ≫
    NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι (fun i => f ⁻¹ᵁ U i)) (FormalCoproduct.mk κ V)
      (coverMap X (fun i => f ⁻¹ᵁ U i) V r hr) Q

theorem naturality {P P' : Presheaves R Y} {Q Q' : Presheaves R X}
    (b : P ⟶ (functor R f).obj Q) (b' : P' ⟶ (functor R f).obj Q')
    (a : P ⟶ P') (c : Q ⟶ Q') (h : b ≫ (functor R f).map c = a ≫ b') :
    (cechComplexFunctor U).map a ≫ SmallRefinedGeometricCechPullback.map R f U V r hr b' =
      SmallRefinedGeometricCechPullback.map R f U V r hr b ≫ (cechComplexFunctor V).map c := by
  let T := cechComplexFunctor (A := ModuleCat.{u} R) U
  have h₁ : T.map a ≫ T.map b' = T.map b ≫ T.map ((functor R f).map c) :=
    (T.map_comp _ _).symm.trans ((congrArg T.map h.symm).trans (T.map_comp _ _))
  have h₂ := Cech.OpenBaseChangeNaturality.CechOpenBaseChangeNaturality.naturality (preimage f) U c
  have h₃ := NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.naturality
    (FormalCoproduct.mk ι (fun i => f ⁻¹ᵁ U i)) (FormalCoproduct.mk κ V)
    (coverMap X (fun i => f ⁻¹ᵁ U i) V r hr) c
  exact three_squares _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃

end Maps

section Complexes
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.Opens) (V : κ → X.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f ⁻¹ᵁ U (r i))

local instance (Z : Scheme.{u}) {ν : Type} (W : ν → Z.Opens) :
    (cechComplexFunctor (A := ModuleCat.{u} R) W).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (A := ModuleCat.{u} R) (FormalCoproduct.mk ν W).cech).Additive
  infer_instance

def bicomplexMap {K : CochainComplex (Presheaves R Y) ℕ}
    {L : CochainComplex (Presheaves R X) ℕ}
    (b : K ⟶ ((functor R f).mapHomologicalComplex (.up ℕ)).obj L) :
    ((cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((cechComplexFunctor V).mapHomologicalComplex (.up ℕ)).obj L where
  f n := SmallRefinedGeometricCechPullback.map R f U V r hr (b.f n)
  comm' n m _ := (naturality R f U V r hr (b.f n) (b.f m) (K.d n m) (L.d n m) (b.comm n m)).symm

theorem bicomplex_naturality
    {K K' : CochainComplex (Presheaves R Y) ℕ}
    {L L' : CochainComplex (Presheaves R X) ℕ}
    (b : K ⟶ ((functor R f).mapHomologicalComplex (.up ℕ)).obj L)
    (b' : K' ⟶ ((functor R f).mapHomologicalComplex (.up ℕ)).obj L')
    (a : K ⟶ K') (c : L ⟶ L')
    (h : b ≫ ((functor R f).mapHomologicalComplex (.up ℕ)).map c = a ≫ b') :
    ((cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).map a ≫ bicomplexMap R f U V r hr b' =
      bicomplexMap R f U V r hr b ≫ ((cechComplexFunctor V).mapHomologicalComplex (.up ℕ)).map c := by
  ext n : 1
  exact naturality R f U V r hr (b.f n) (b'.f n) (a.f n) (c.f n) (congrArg (fun k => k.f n) h)

end Complexes

theorem product_projection {A : Type*} [Category* A] {α : Type*} {β : Type*}
    [HasProductsOfShape α A] [HasProductsOfShape β A]
    (X Y Z : α → A) (W : β → A) (b : ∀ i, X i ⟶ Y i) (e : ∀ i, Y i ≅ Z i)
    (r : β → α) (a : ∀ j, Z (r j) ⟶ W j) (t : β) :
    (Limits.Pi.map b ≫ (Pi.mapIso e).hom ≫ Pi.lift (fun j => Pi.π Z (r j) ≫ a j)) ≫ Pi.π W t =
      Pi.π X (r t) ≫ b (r t) ≫ (e (r t)).hom ≫ a t := by
  simp only [Category.assoc, Pi.lift_comp_π, Pi.mapIso_hom_π_assoc, Pi.map_π_assoc]

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.Opens) (V : κ → X.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f ⁻¹ᵁ U (r i))

def intersectionHom (n : ℕ) (t : Fin (n + 1) → κ) :
    (∏ᶜ (V ∘ t)) ⟶ f ⁻¹ᵁ (∏ᶜ (U ∘ (r ∘ t))) :=
  ((FormalCoproduct.cechFunctor.map (coverMap X (fun i => f ⁻¹ᵁ U i) V r hr)).app
    (op ⦋n⦌)).φ t ≫ (PreservesProduct.iso (preimage f) (U ∘ (r ∘ t))).inv

theorem map_f_π {P : Presheaves R Y} {Q : Presheaves R X}
    (b : P ⟶ (functor R f).obj Q) (n : ℕ) (t : Fin (n + 1) → κ) :
    (SmallRefinedGeometricCechPullback.map R f U V r hr b).f n ≫ Pi.π (fun t : Fin (n + 1) → κ => Q.obj (op (∏ᶜ (V ∘ t)))) t =
      Pi.π (fun s : Fin (n + 1) → ι => P.obj (op (∏ᶜ (U ∘ s)))) (r ∘ t) ≫
        b.app (op (∏ᶜ (U ∘ (r ∘ t)))) ≫ Q.map (intersectionHom f U V r hr n t).op := by
  let a : FormalCoproduct.mk (Fin (n + 1) → κ) (fun t => ∏ᶜ (V ∘ t)) ⟶
      FormalCoproduct.mk (Fin (n + 1) → ι) (fun t => ∏ᶜ (fun i => f ⁻¹ᵁ U (t i))) :=
    (FormalCoproduct.cechFunctor.map (coverMap X (fun i => f ⁻¹ᵁ U i) V r hr)).app (op ⦋n⦌)
  let P₀ := fun s : Fin (n + 1) → ι => P.obj (op (∏ᶜ (U ∘ s)))
  let M₀ := fun s : Fin (n + 1) → ι => Q.obj (op (f ⁻¹ᵁ (∏ᶜ (U ∘ s))))
  let N₀ := fun s : Fin (n + 1) → ι => Q.obj (op (∏ᶜ (fun i => f ⁻¹ᵁ U (s i))))
  let T₀ := fun s : Fin (n + 1) → κ => Q.obj (op (∏ᶜ (V ∘ s)))
  let b₀ : ∀ s, P₀ s ⟶ M₀ s := fun s => b.app (op (∏ᶜ (U ∘ s)))
  let e : ∀ s, M₀ s ≅ N₀ s := fun s =>
    Q.mapIso (PreservesProduct.iso (preimage f) (U ∘ s)).symm.op
  let a₀ : ∀ s, N₀ (r ∘ s) ⟶ T₀ s := fun s => Q.map (a.φ s).op
  have hx := product_projection P₀ M₀ N₀ T₀ b₀ e (fun s => r ∘ s) a₀ t
  have hc : (e (r ∘ t)).hom ≫ a₀ t = Q.map (intersectionHom f U V r hr n t).op :=
    (Q.map_comp (PreservesProduct.iso (preimage f) (U ∘ (r ∘ t))).symm.op.hom
      (a.φ t).op).symm
  exact hx.trans (congrArg (fun k => Pi.π P₀ (r ∘ t) ≫ b₀ (r ∘ t) ≫ k) hc)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.RefinedGeometricCechPullback.SmallRefinedGeometricCechPullback
