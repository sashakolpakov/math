import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechPullback
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits

/-! # Complex Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ComplexPullback.CechPullback

noncomputable section

/-! The actual direct Čech pullback acts on complexes of presheaves and respects commuting squares. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
  {ι κ : Type u} (U : ι → Y.Opens) (V : κ → X.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f ⁻¹ᵁ U (r i))

local instance (Z : Scheme.{u}) {ν : Type u} (W : ν → Z.Opens) :
    (cechComplexFunctor (A := ModuleCat.{u} R) W).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (A := ModuleCat.{u} R) (FormalCoproduct.mk ν W).cech).Additive
  infer_instance

def bicomplexMap {K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R Y) ℕ}
    {L : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X) ℕ}
    (b : K ⟶ ((Image.CechImage.functor R f).mapHomologicalComplex (.up ℕ)).obj L) :
    ((cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((cechComplexFunctor V).mapHomologicalComplex (.up ℕ)).obj L where
  f n := CechPullback.map R f U V r hr (b.f n)
  comm' n m _ := (CechPullback.naturality R f U V r hr (b.f n) (b.f m) (K.d n m) (L.d n m) (b.comm n m)).symm

theorem bicomplex_naturality
    {K K' : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R Y) ℕ}
    {L L' : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X) ℕ}
    (b : K ⟶ ((Image.CechImage.functor R f).mapHomologicalComplex (.up ℕ)).obj L)
    (b' : K' ⟶ ((Image.CechImage.functor R f).mapHomologicalComplex (.up ℕ)).obj L')
    (a : K ⟶ K') (c : L ⟶ L')
    (h : b ≫ ((Image.CechImage.functor R f).mapHomologicalComplex (.up ℕ)).map c = a ≫ b') :
    ((cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).map a ≫ bicomplexMap R f U V r hr b' =
      bicomplexMap R f U V r hr b ≫ ((cechComplexFunctor V).mapHomologicalComplex (.up ℕ)).map c := by
  ext n : 1
  exact CechPullback.naturality R f U V r hr (b.f n) (b'.f n) (a.f n) (c.f n) (congrArg (fun k => k.f n) h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ComplexPullback.CechPullback
