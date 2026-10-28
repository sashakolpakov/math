import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionContraction

/-! # Complex Iso -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ComplexIso

noncomputable section

/-! # A termwise complete complex is isomorphic to its actual adic completion -/

open _root_.CategoryTheory

universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (C : CochainComplex (ModuleCat.{u} R) ℕ)

def inclusion : C ⟶ AdicCompletionContraction.complex I C where
  f n := ModuleCat.ofHom (AdicCompletion.of I (C.X n))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact AdicCompletion.map_of I (C.d i j).hom x

theorem inclusion_natural {D : CochainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D) :
    inclusion I C ≫ ((AdicCompletionLinear.functor I).mapHomologicalComplex (.up ℕ)).map f =
      f ≫ inclusion I D := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact AdicCompletion.map_of I (f.f n).hom x

variable (hC : ∀ n, IsAdicComplete I (C.X n))

def complexIso : C ≅ AdicCompletionContraction.complex I C := by
  letI (n : ℕ) : IsAdicComplete I (C.X n) := hC n
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n => (AdicCompletion.ofLinearEquiv I (C.X n)).toModuleIso)
    (fun i j hij => (inclusion I C).comm' i j hij)

theorem complexIso_hom : (complexIso I C hC).hom = inclusion I C := by
  rfl

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ComplexIso
