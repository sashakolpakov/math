import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Semilinear Complex Restriction -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction

noncomputable section

/-! # An actual semilinear complex map is linear into the scalar-restricted target -/

open _root_.CategoryTheory OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap

universe u
variable {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S}
  {C : CochainComplex (ModuleCat.{u} R) ℕ} {D : CochainComplex (ModuleCat.{u} S) ℕ}

def restrictedComplex (φ : R →+* S) (D : CochainComplex (ModuleCat.{u} S) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℕ)).obj D

def linearMap (f : SemilinearComplexMap.Map φ C D) : C ⟶ restrictedComplex φ D where
  f n := ModuleCat.ofHom (X := C.X n) (Y := (restrictedComplex φ D).X n) {
    toFun := f.f n
    map_add' := map_add (f.f n)
    map_smul' := (f.f n).map_smulₛₗ }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (f.comm i j x).symm

theorem linearMap_apply (f : SemilinearComplexMap.Map φ C D) (n : ℕ) (x : C.X n) :
    ((linearMap f).f n).hom x = f.f n x := rfl

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction
