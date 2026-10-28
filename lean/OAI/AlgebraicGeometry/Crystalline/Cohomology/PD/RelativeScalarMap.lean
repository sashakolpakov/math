import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamSemilinearMap
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction

/-! # Relative Scalar Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.RelativeScalarMap.PDRelativeScalarMap

noncomputable section

/-! # Relative PD pullback over a common smaller coefficient ring -/

open _root_.CategoryTheory

universe u

variable (W R S A B : Type u) [CommRing W] [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Algebra W R] [Algebra W S] [Algebra R A] [Algebra S B]
  (φ : R →+* S) (hW : ∀ w, φ (algebraMap W R w) = algebraMap W S w)
  (f : A →+* B) (h : ∀ r, f (algebraMap R A r) = algebraMap S B (φ r))
  (I : Ideal A) (δ : DividedPowers I) (J : Ideal B) (ε : DividedPowers J)
  (hf : DividedPowers.IsDPMorphism δ ε f)

local notation "C" => OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex
  (algebraMap W R) (DeRham.PDDeRham.complex R A I δ)
local notation "D" => OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex
  (algebraMap W S) (DeRham.PDDeRham.complex S B J ε)

def component (n : ℕ) : (C).X n ⟶ (D).X n := ModuleCat.ofHom (X := (C).X n) (Y := (D).X n) {
  toFun := DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap R S A B φ f h I δ J ε hf n
  map_add' := map_add _
  map_smul' w ω := by
    change DeRham.PDDeRham.Form R A I δ n at ω
    change DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap R S A B φ f h I δ J ε hf n
      (algebraMap W R w • ω) = algebraMap W S w • _
    rw [map_smulₛₗ, hW] }

def complexMap : C ⟶ D where
  f := component W R S A B φ hW f h I δ J ε hf
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ((DeRhamSemilinearMap.PDDeRhamSemilinearMap.complexMap R S A B φ f h I δ J ε hf).comm i j x).symm

theorem symbol (n : ℕ) (a : A) (v : Fin n → A) :
    ((complexMap W R S A B φ hW f h I δ J ε hf).f n).hom (DeRham.PDDeRham.symbol R A I δ a v) =
      DeRham.PDDeRham.symbol S B J ε (f a) (f ∘ v) :=
  DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap_symbol R S A B φ f h I δ J ε hf n a v

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.RelativeScalarMap.PDRelativeScalarMap
