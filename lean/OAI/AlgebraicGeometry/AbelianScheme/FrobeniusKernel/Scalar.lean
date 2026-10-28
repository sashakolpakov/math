import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteTorsion

/-! # Scalar -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Scalar.Construction

noncomputable section

/-!
Frobenius having scalar image is independent of a choice of coordinates
or group law. For a native finite group scheme, its extracted Hopf counit
identifies those scalars and proves that relative Frobenius is trivial.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

section Algebra

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [CharP k p]
variable [CommRing A] [HopfAlgebra k A]

omit [Fact p.Prime] [CharP k p] in
theorem hopfHeightOne_of_scalar_powers
    (h : ∀ a : A, ∃ c : k, a ^ p = algebraMap k A c) : HeightOneTorsion.Construction.HopfHeightOne p k A := by
  intro a
  obtain ⟨c, hc⟩ := h a
  have hε : Coalgebra.counit (R := k) (algebraMap k A c) = c := by
    change (Bialgebra.counitAlgHom k A) (algebraMap k A c) = c
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
      (Bialgebra.counitAlgHom k A).commutes c
  have he : Coalgebra.counit (R := k) a ^ p = c :=
    (Bialgebra.counit_pow a p).symm.trans ((congrArg (Coalgebra.counit (R := k)) hc).trans hε)
  exact hc.trans (congrArg (algebraMap k A) he.symm)

end Algebra

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
variable (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
variable [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
variable (B : Type u) [CommRing B] [Algebra k B]

/-- A scalar-image coordinate model proves trivial relative Frobenius
for the original group scheme, regardless of its presentation. -/
theorem finiteGroup_frobenius_of_scalar_powers
    (e : G.X ≅ (Spec (.of B)).asOver (Spec (.of k)))
    (hB : ∀ b : B, ∃ c : k, b ^ p = algebraMap k B c) :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) G.X = 1 := by
  let P := CartierModel.Construction.cartierCoordinates (.of k) G
  have : Coalgebra.IsCocomm k P.algebra := P.cocommutative
  let e' : (algSpec (.of k)).obj (op (CommAlgCat.of k P.algebra)) ≅
      (algSpec (.of k)).obj (op (CommAlgCat.of k B)) :=
    (Grp.forget (Over (Spec (.of k)))).mapIso P.comparison ≪≫ e
  let a := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimageIso e'
  let φ : B ≃ₐ[k] P.algebra := CommAlgCat.algEquivOfIso a.unop
  have hP : ∀ b : P.algebra, ∃ c : k, b ^ p = algebraMap k P.algebra c := by
    intro b
    obtain ⟨c, hc⟩ := hB (φ.symm b)
    refine ⟨c, ?_⟩
    calc
      b ^ p = φ ((φ.symm b) ^ p) := by rw [map_pow, φ.apply_symm_apply]
      _ = φ (algebraMap k B c) := congrArg φ hc
      _ = algebraMap k P.algebra c := φ.commutes c
  have hF := HeightOne.Construction.trivial_frobenius_of_hopfHeightOne p k P.algebra
    (hopfHeightOne_of_scalar_powers p k P.algebra hP)
  exact FiniteTorsion.Construction.trivialFrobenius_of_groupIso p (Fact.out : p.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) P.comparison.symm hF

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Scalar.Construction
