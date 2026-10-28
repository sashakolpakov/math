import OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarExtensionBase
import OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtensionExact
import OAI.AlgebraicGeometry.Crystalline.Cohomology.TwistedHomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.TwistedConjugation

/-! # Scalar Extension On -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarExtensionOn.ScalarExtensionTwistedHomology

noncomputable section

/-! # Canonical homology transport for scalar-extended twisted complexes -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (e : R ≃+* R) (t : S ≃+* S)
  (h : ∀ r, t (algebraMap R S r) = algebraMap R S (e r))

local notation "Q" => ModuleCat.restrictScalars e.toRingHom
local notation "T" => ModuleCat.restrictScalars t.toRingHom
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension.functor R S

variable (K : CochainComplex (ModuleCat.{u} R) ℕ)

def map (f : K ⟶ ((Q).mapHomologicalComplex (.up ℕ)).obj K) :
    ((P).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((T).mapHomologicalComplex (.up ℕ)).obj (((P).mapHomologicalComplex (.up ℕ)).obj K) :=
  ((P).mapHomologicalComplex (.up ℕ)).map f ≫
    ((Functor.mapHomologicalComplexCompIso (ScalarExtensionBase.ScalarExtensionTwist.iso R S e t h) (.up ℕ)).app K).hom

theorem component (f : K ⟶ ((Q).mapHomologicalComplex (.up ℕ)).obj K)
    (j : ℕ) (s : S) (x : K.X j) :
    (ScalarExtensionTwistedHomology.map R S e t h K f).f j (s ⊗ₜ[R] x) =
      ScalarExtensionBase.ScalarExtensionTwist.tensor R S (K.X j) (t s) (f.f j x) := rfl

variable [Module.Flat R S]

theorem square (f : K ⟶ ((Q).mapHomologicalComplex (.up ℕ)).obj K) (n : ℕ) :
    HomologicalComplex.homologyMap (ScalarExtensionTwistedHomology.map R S e t h K f) n ≫
        (Mapped.ComplexHomology.MappedComplexHomology.iso T (((P).mapHomologicalComplex (.up ℕ)).obj K) n).hom ≫
        (T).map (Mapped.ComplexHomology.MappedComplexHomology.iso P K n).hom =
      (Mapped.ComplexHomology.MappedComplexHomology.iso P K n).hom ≫
        (P).map (HomologicalComplex.homologyMap f n ≫ (Mapped.ComplexHomology.MappedComplexHomology.iso Q K n).hom) ≫
        (ScalarExtensionBase.ScalarExtensionTwist.iso R S e t h).hom.app (K.homology n) :=
  TwistedHomology.TwistedHomologyTransport.homology_square Q T P (ScalarExtensionBase.ScalarExtensionTwist.iso R S e t h) K f n

omit [Module.Flat R S] in
private theorem component_apply {M : ModuleCat.{u} R} (f : M ⟶ (Q).obj M) (s : S) (x : M) :
    ((P).map f ≫ (ScalarExtensionBase.ScalarExtensionTwist.iso R S e t h).hom.app M).hom (s ⊗ₜ[R] x) =
      ScalarExtensionBase.ScalarExtensionTwist.tensor R S M (t s) (f.hom x) := rfl

theorem on_tensor (f : K ⟶ ((Q).mapHomologicalComplex (.up ℕ)).obj K)
    (n : ℕ) (s : S) (x : K.homology n) :
    (Mapped.ComplexHomology.MappedComplexHomology.iso P K n).hom
      ((Mapped.ComplexHomology.MappedComplexHomology.iso T (((P).mapHomologicalComplex (.up ℕ)).obj K) n).hom
        (HomologicalComplex.homologyMap (ScalarExtensionTwistedHomology.map R S e t h K f) n
          ((Mapped.ComplexHomology.MappedComplexHomology.iso P K n).inv (s ⊗ₜ[R] x)))) =
      ScalarExtensionBase.ScalarExtensionTwist.tensor R S (K.homology n) (t s)
        ((Mapped.ComplexHomology.MappedComplexHomology.iso Q K n).hom (HomologicalComplex.homologyMap f n x)) := by
  let c := Mapped.ComplexHomology.MappedComplexHomology.iso P K n
  let g := HomologicalComplex.homologyMap f n ≫ (Mapped.ComplexHomology.MappedComplexHomology.iso Q K n).hom
  let f' := HomologicalComplex.homologyMap (ScalarExtensionTwistedHomology.map R S e t h K f) n ≫
    (Mapped.ComplexHomology.MappedComplexHomology.iso T (((P).mapHomologicalComplex (.up ℕ)).obj K) n).hom
  let g' := (P).map g ≫ (ScalarExtensionBase.ScalarExtensionTwist.iso R S e t h).hom.app (K.homology n)
  have hs : f' ≫ (T).map c.hom = c.hom ≫ g' :=
    (Category.assoc (HomologicalComplex.homologyMap (ScalarExtensionTwistedHomology.map R S e t h K f) n)
      (Mapped.ComplexHomology.MappedComplexHomology.iso T (((P).mapHomologicalComplex (.up ℕ)).obj K) n).hom
      ((T).map c.hom)).trans (square R S e t h K f n)
  have hc := Cohomology.Module.TwistedConjugation.ModuleTwistedConjugation.apply t.toRingHom c f' g' hs (s ⊗ₜ[R] x)
  exact hc.trans (component_apply R S e t h g s x)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarExtensionOn.ScalarExtensionTwistedHomology
