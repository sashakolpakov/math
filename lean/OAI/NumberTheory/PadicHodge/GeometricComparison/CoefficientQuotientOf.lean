import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient

/-! # Coefficient Quotient Of -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientQuotientOf.CoefficientQuotientLift

noncomputable section

/-! Cochain maps annihilating a coefficient ideal descend canonically
to the actual coefficient quotient complex, naturally in commuting squares. -/

open _root_.CategoryTheory

universe u v
variable (R : Type u) [CommRing R] (I : Ideal R)
  {K L : CochainComplex (ModuleCat.{v} R) ℕ} (a : K ⟶ L)
  (h : ∀ n, (I • ⊤ : Submodule R (K.X n)) ≤ LinearMap.ker (a.f n).hom)

def map : IntegralComparison.Module.IdealQuotient.complex R I K ⟶ L where
  f n := ModuleCat.ofHom ((I • ⊤ : Submodule R (K.X n)).liftQ (a.f n).hom (h n))
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (I • ⊤ : Submodule R (K.X n)).mkQ_surjective x
    exact congrArg (fun f : K.X n ⟶ L.X m => f x) (a.comm n m)

theorem factorization : IntegralComparison.Module.IdealQuotient.complexProjection R I K ≫ CoefficientQuotientLift.map R I a h = a := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem unique (b : IntegralComparison.Module.IdealQuotient.complex R I K ⟶ L)
    (hb : IntegralComparison.Module.IdealQuotient.complexProjection R I K ≫ b = a) : CoefficientQuotientLift.map R I a h = b := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (I • ⊤ : Submodule R (K.X n)).mkQ_surjective x
  exact (congrArg (fun q : K.X n ⟶ L.X n => q x) (congrArg (fun q => q.f n) hb)).symm

theorem kernel_of_annihilation (hL : ∀ n r, r ∈ I → ∀ x : L.X n, r • x = 0) (n : ℕ) :
    (I • ⊤ : Submodule R (K.X n)) ≤ LinearMap.ker (a.f n).hom := by
  apply Submodule.smul_le.mpr
  intro r hr x _
  exact ((a.f n).hom.map_smul r x).trans (hL n r hr (a.f n x))

variable {K' L' : CochainComplex (ModuleCat.{v} R) ℕ} (b : K' ⟶ L')
  (h' : ∀ n, (I • ⊤ : Submodule R (K'.X n)) ≤ LinearMap.ker (b.f n).hom)
  (f : K ⟶ K') (g : L ⟶ L') (hsquare : a ≫ g = f ≫ b)

include hsquare in
theorem naturality : CoefficientQuotientLift.map R I a h ≫ g =
    (((IntegralComparison.Module.IdealQuotient.functor R I).mapHomologicalComplex (.up ℕ)).map f) ≫ CoefficientQuotientLift.map R I b h' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (I • ⊤ : Submodule R (K.X n)).mkQ_surjective x
  exact congrArg (fun q : K.X n ⟶ L'.X n => q x) (congrArg (fun q => q.f n) hsquare)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientQuotientOf.CoefficientQuotientLift
