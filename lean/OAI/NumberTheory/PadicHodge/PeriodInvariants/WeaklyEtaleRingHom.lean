import OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleAffine

/-! # Weakly Etale Ring Hom -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleRingHom

noncomputable section

/-! # Weakly etale ring maps with their actual affine scheme morphisms -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def Property (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Algebra.WeaklyEtale R S

theorem algebraMap_iff [Algebra R S] : Property (algebraMap R S) ↔ Algebra.WeaklyEtale R S := by
  rw [Property, toAlgebra_algebraMap]

theorem specMap (f : R →+* S) (hf : Property f) : WeaklyEtale (Spec.map (CommRingCat.ofHom f)) := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.WeaklyEtale R S := hf
  exact WeaklyEtaleAffine.specMap R S

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleRingHom
