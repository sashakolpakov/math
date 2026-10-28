import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamComplexMap

/-! # De Rham Algebra Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamAlgebraCoordinates

noncomputable section

/-! Equal presentations of an algebra action give canonical
coordinates for the same PD de Rham complex, naturally in PD maps. -/

open _root_.CategoryTheory

universe u
variable (R A : Type u) [CommRing R] [CommRing A]
  (I : Ideal A) (δ : DividedPowers I)

def complex (a : Algebra R A) : CochainComplex (ModuleCat.{u} R) ℕ :=
  @AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A _ _ a I δ

def iso (a a' : Algebra R A) (h : a = a') :
    complex R A I δ a ≅ complex R A I δ a' :=
  eqToIso (congrArg (complex R A I δ) h)

theorem iso_hom_symbol (a a' : Algebra R A) (h : a = a')
    (n : ℕ) (b : A) (v : Fin n → A) :
    (iso R A I δ a a' h).hom.f n (@AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A _ _ a I δ n b v) =
      @AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A _ _ a' I δ n b v := by
  subst a'
  rfl

variable (B : Type u) [CommRing B] (J : Ideal B) (ε : DividedPowers J)

def map (a : Algebra R A) (b : Algebra R B) (f : A →+* B)
    (hf : ∀ r, f (@algebraMap R A _ _ a r) = @algebraMap R B _ _ b r)
    (hδ : DividedPowers.IsDPMorphism δ ε f) :
    complex R A I δ a ⟶ complex R B J ε b := by
  letI : Algebra R A := a
  letI : Algebra R B := b
  let φ : A →ₐ[R] B := { f with commutes' := hf }
  exact DeRhamComplexMap.map (CommAlgCat.ofHom φ) hδ

theorem naturality (a a' : Algebra R A) (b b' : Algebra R B)
    (ha : a = a') (hb : b = b') (f : A →+* B)
    (hf : ∀ r, f (@algebraMap R A _ _ a r) = @algebraMap R B _ _ b r)
    (hf' : ∀ r, f (@algebraMap R A _ _ a' r) = @algebraMap R B _ _ b' r)
    (hδ : DividedPowers.IsDPMorphism δ ε f) :
    map R A I δ B J ε a b f hf hδ ≫ (iso R B J ε b b' hb).hom =
      (iso R A I δ a a' ha).hom ≫ map R A I δ B J ε a' b' f hf' hδ := by
  subst a'
  subst b'
  simp only [iso, eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamAlgebraCoordinates
