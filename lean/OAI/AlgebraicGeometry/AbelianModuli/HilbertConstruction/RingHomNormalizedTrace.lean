import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.TracePushout

/-! # Ring Hom Normalized Trace -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingHomNormalizedTrace

noncomputable section

/-! A version of normalized trace for explicit ring homomorphisms, compatible with pushout squares. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u

def ringHomNormalizedTrace {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (u : Rˣ) : A → R :=
  @Normalized.AlgebraTrace.normalizedAlgebraTrace R A _ _ f.toAlgebra u

theorem ringHomNormalizedTrace_pushout {R A S B : Type u}
    [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    (f : R →+* A) (g : R →+* S) (k : A →+* B) (l : S →+* B)
    (h : IsPushout (CommRingCat.ofHom g) (CommRingCat.ofHom f)
      (CommRingCat.ofHom l) (CommRingCat.ofHom k))
    {ι : Type*} [Fintype ι] (b : @Module.Basis ι R A _ _ f.toModule)
    (u : Rˣ) (a : A) :
    ringHomNormalizedTrace l (Units.map g u) (k a) = g (ringHomNormalizedTrace f u a) := by
  let : Algebra R A := f.toAlgebra
  let : Algebra R S := g.toAlgebra
  let : Algebra A B := k.toAlgebra
  let : Algebra S B := l.toAlgebra
  let : Algebra R B := (k.comp f).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom h.w.symm)
  exact Normalized.TracePushout.normalizedAlgebraTrace_of_isPushout b h u a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingHomNormalizedTrace
