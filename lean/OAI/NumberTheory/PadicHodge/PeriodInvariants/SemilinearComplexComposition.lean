import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap

/-! # Semilinear Complex Composition -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexComposition

/-! # Composition of actual semilinear complex maps with linear comparison maps -/

open _root_.CategoryTheory OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap

universe u
variable {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S}
  {C : CochainComplex (ModuleCat.{u} R) ℕ} {D E : CochainComplex (ModuleCat.{u} S) ℕ}

def postcompLinear (f : SemilinearComplexMap.Map φ C D) (e : D ⟶ E) : SemilinearComplexMap.Map φ C E where
  f n := (e.f n).hom.comp (f.f n)
  comm i j x := by
    change (e.f j).hom (f.f j ((C.d i j).hom x)) = (E.d i j).hom ((e.f i).hom (f.f i x))
    rw [f.comm]
    exact (congrArg (fun k : D.X i ⟶ E.X j => k.hom (f.f i x)) (e.comm i j)).symm

variable {B : CochainComplex (ModuleCat.{u} R) ℕ}

def precompLinear (e : B ⟶ C) (f : SemilinearComplexMap.Map φ C D) : SemilinearComplexMap.Map φ B D where
  f n := (f.f n).comp (e.f n).hom
  comm i j x :=
    (congrArg (f.f j) (congrArg (fun k : B.X i ⟶ C.X j => k.hom x) (e.comm i j)).symm).trans
      (f.comm i j ((e.f i).hom x))

end OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexComposition
