import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernelExhaustion
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Verschiebung
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Etale

/-! # Frobenius Kernel Exhaustion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FrobeniusKernelExhaustion

noncomputable section

/-! The actual Verschiebung kills the Frobenius transform of every
etale q-torsion subgroup. Consequently a supported Frobenius composite
whose second kernel is such a subgroup has no additional higher-torsion
points. All statements retain arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernelExhaustion

variable (q : ℕ) [Fact q.Prime] (k : Type u) [Field k] [CharP k q] [PerfectRing k q]
variable (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [Smooth A.hom]
variable {E : Over (Spec (.of k))} [Etale E.hom] (i : E ⟶ A) (hi : i ^ q = 1)

include hi in
theorem verschiebung_kills_etale_qtorsion :
    (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q Fact.out (Spec (.of k))
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map i ≫ Picard.Homomorphisms.Verschiebung.Construction.verschiebung q k A = 1 := by
  let hS := Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)
  have hleft : IsIso (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out hS E).left := Picard.Homomorphisms.Etale.Construction.relativeFrobenius_isIso_of_etale q Fact.out hS E
  have : IsIso ((Over.forget (Spec (.of k))).map (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out hS E)) := hleft
  have hF : IsIso (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out hS E) :=
    isIso_of_reflects_iso (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out hS E) (Over.forget _)
  let w : E ≅ Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist q Fact.out hS E :=
    @asIso _ _ _ _ (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out hS E) hF
  exact MixedKernelExhaustion.complement_kills_transported_torsion (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out hS A)
    (Picard.Homomorphisms.Verschiebung.Construction.verschiebung q k A) q (Picard.Homomorphisms.Verschiebung.Construction.frobenius_comp_verschiebung q k A) i
    ((Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q Fact.out (Spec (.of k)) hS)).map i)
    w
    ((Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat q Fact.out hS).naturality i).symm hi

variable {C : Over (Spec (.of k))} [GrpObj C]

include hi in
theorem supported_frobenius_composite_killed
    (p : A ⟶ A)
    (g : Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist q Fact.out (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A ⟶ C)
    (hsecond : ∀ (T : Over (Spec (.of k)))
      (b : T ⟶ Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist q Fact.out (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A),
      b ≫ (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q Fact.out (Spec (.of k))
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map p = b → b ≫ g = 1 →
      ∃ h : T ⟶ Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist q Fact.out (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) E,
        h ≫ (Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q Fact.out (Spec (.of k))
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map i = b)
    (T : Over (Spec (.of k))) (a : T ⟶ A) (ha : a ≫ p = a)
    (hk : a ≫ Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A ≫ g = 1) : a ^ q = 1 :=
  MixedKernelExhaustion.supported_composite_kernel_killed
    (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A)
    (Picard.Homomorphisms.Verschiebung.Construction.verschiebung q k A) g q (Picard.Homomorphisms.Verschiebung.Construction.frobenius_comp_verschiebung q k A)
    p ((Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q Fact.out (Spec (.of k))
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map p)
    ((Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat q Fact.out (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))).naturality p)
    ((Over.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q Fact.out (Spec (.of k))
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))).map i)
    (verschiebung_kills_etale_qtorsion q k A i hi) hsecond T a ha hk

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FrobeniusKernelExhaustion
