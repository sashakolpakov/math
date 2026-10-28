import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryCoordinateLinear
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientGraphs
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Multiplicative
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteTorsion

/-! # Ordinary Kernel Specialization -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The identity factor of the constructed ordinary model has trivial
special Frobenius. Every integral etale graph character therefore
specializes to the identity-valued morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientGraphs
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

universe u

theorem OrdinaryKernelSpecialization.Lifts.perfectField_absoluteFrobenius_isIso (q : ℕ) [Fact q.Prime]
    (k : Type u) [Field k] [CharP k q] [PerfectRing k q] :
    IsIso (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of k))
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))) := by
  rw [Picard.Homomorphisms.Affine.Construction.absoluteFrobenius_spec q (Fact.out : q.Prime) k (CharP.cast_eq_zero k q)]
  have h : Picard.Homomorphisms.Frobenius.Construction.powerRingHom q (Fact.out : q.Prime) k (CharP.cast_eq_zero k q) =
      (frobeniusEquiv k q).toRingHom := RingHom.ext (fun _ => rfl)
  rw [h]
  have : IsIso (CommRingCat.ofHom (frobeniusEquiv k q).toRingHom) :=
    inferInstanceAs (IsIso (frobeniusEquiv k q).toCommRingCatIso.hom)
  infer_instance

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] (q : ℕ) [Fact q.Prime]
  (A : Grp (Over (Spec (.of R)))) (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)
  [CharP (IsLocalRing.ResidueField R) q]

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.identity_special_frobenius :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q (Fact.out : q.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (IsLocalRing.ResidueField R)
        (CharP.cast_eq_zero (IsLocalRing.ResidueField R) q))
      ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj C.identity.X) = 1 :=
  AbelianScheme.FrobeniusKernel.FiniteTorsion.Construction.trivialFrobenius_of_groupIso q (Fact.out : q.Prime) _ C.special
    (AbelianScheme.FrobeniusKernel.Multiplicative.Construction.ordinaryMultiplicative_relativeFrobenius q (IsLocalRing.ResidueField R) 1)

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.character_specializes_zero
    [PerfectRing (IsLocalRing.ResidueField R) q]
    {H : Over (Spec (.of R))} [Etale H.hom] (χ : H ⟶ C.identity.X) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map χ = 1 := by
  have := OrdinaryKernelSpecialization.Lifts.perfectField_absoluteFrobenius_isIso q (IsLocalRing.ResidueField R)
  have : Etale ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj H).hom := by
    dsimp
    infer_instance
  exact QuotientGraphs.etale_to_frobenius_killed q (Fact.out : q.Prime) _
    (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.identity_special_frobenius R L q A C) _

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
