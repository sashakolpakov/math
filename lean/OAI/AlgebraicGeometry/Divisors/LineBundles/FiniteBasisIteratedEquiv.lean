import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Integral

/-! # Finite Basis Iterated Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteBasisIteratedEquiv.BundleCycles

noncomputable section

section

/-! Explicit iterated augmentation supplies finite free modules
of each positive rank, with actual bases and projective charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def iteratedAugmentedModule (R : Type) : ℕ → Type
  | 0 => R
  | n + 1 => R × iteratedAugmentedModule R n

instance iteratedAugmentedModule_addCommGroup (R : Type) [CommRing R] :
    (n : ℕ) → AddCommGroup (BundleCycles.iteratedAugmentedModule R n)
  | 0 => inferInstanceAs (AddCommGroup R)
  | n + 1 => by
    let := iteratedAugmentedModule_addCommGroup R n
    exact inferInstanceAs (AddCommGroup (R × BundleCycles.iteratedAugmentedModule R n))

instance iteratedAugmentedModule_module (R : Type) [CommRing R] :
    (n : ℕ) → Module R (BundleCycles.iteratedAugmentedModule R n)
  | 0 => inferInstanceAs (Module R R)
  | n + 1 => by
    let := iteratedAugmentedModule_module R n
    exact inferInstanceAs (Module R (R × BundleCycles.iteratedAugmentedModule R n))

def iteratedAugmentedIndex : ℕ → Type
  | 0 => Unit
  | n + 1 => Unit ⊕ iteratedAugmentedIndex n

instance iteratedAugmentedIndex_fintype : (n : ℕ) → Fintype (BundleCycles.iteratedAugmentedIndex n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    let := iteratedAugmentedIndex_fintype n
    exact inferInstanceAs (Fintype (Unit ⊕ BundleCycles.iteratedAugmentedIndex n))

instance iteratedAugmentedIndex_nonempty : (n : ℕ) → Nonempty (BundleCycles.iteratedAugmentedIndex n)
  | 0 => ⟨()⟩
  | _ + 1 => ⟨Sum.inl ()⟩

def iteratedAugmentedBasis (R : Type) [CommRing R] :
    (n : ℕ) → Module.Basis (BundleCycles.iteratedAugmentedIndex n) R (BundleCycles.iteratedAugmentedModule R n)
  | 0 => Module.Basis.singleton Unit R
  | n + 1 => (Module.Basis.singleton Unit R).prod (iteratedAugmentedBasis R n)

theorem iteratedAugmentedIndex_card (n : ℕ) : Nat.card (BundleCycles.iteratedAugmentedIndex n) = n + 1 := by
  induction n with
  | zero => exact Nat.card_eq_fintype_card.trans rfl
  | succ n ih =>
    change Nat.card (Unit ⊕ BundleCycles.iteratedAugmentedIndex n) = (n + 1) + 1
    rw [Nat.card_sum, Nat.card_unique, ih]
    omega

instance iteratedAugmentedModule_finite (R : Type) [CommRing R] (n : ℕ) :
    Module.Finite R (BundleCycles.iteratedAugmentedModule R n) := Module.Finite.of_basis (BundleCycles.iteratedAugmentedBasis R n)

theorem iteratedProjective_sourceCharts (R : Type) [CommRing R] (n : ℕ) :
    AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (BundleCycles.iteratedAugmentedModule R n)) n := by
  have h := Symmetric.BasisAffineChart.BundleCycles.symmetricProjective_hasAffineSpaceSourceChartsOfRank (BundleCycles.iteratedAugmentedBasis R n)
  rw [iteratedAugmentedIndex_card, Nat.add_sub_cancel] at h
  exact h

instance iteratedProjective_smooth (R : Type) [CommRing R] (n : ℕ) :
    Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (BundleCycles.iteratedAugmentedModule R n)) :=
  (iteratedProjective_sourceCharts R n).forget.smooth

instance iteratedProjective_geometricallyIntegral (R : Type) [CommRing R] (n : ℕ) :
    GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (BundleCycles.iteratedAugmentedModule R n)) :=
  SymmetricProjective.IntegralFibers.BundleCycles.symmetricProjective_geometricallyIntegral (BundleCycles.iteratedAugmentedBasis R n)

instance iteratedAugmentedProjective_smooth (R : Type) [CommRing R] (n : ℕ) :
    Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × BundleCycles.iteratedAugmentedModule R n)) :=
  iteratedProjective_smooth R (n + 1)

instance iteratedAugmentedProjective_geometricallyIntegral (R : Type) [CommRing R] (n : ℕ) :
    GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × BundleCycles.iteratedAugmentedModule R n)) :=
  iteratedProjective_geometricallyIntegral R (n + 1)

end

/-! A finite basis gives an actual linear isomorphism to the
explicit iterated augmented module of the same positive rank. -/

def finiteBasisIteratedEquiv {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (n : ℕ) (hn : Nat.card ι = n + 1) :
    M ≃ₗ[R] BundleCycles.iteratedAugmentedModule R n :=
  b.equiv (BundleCycles.iteratedAugmentedBasis R n) (Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hn, iteratedAugmentedIndex_card]))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteBasisIteratedEquiv.BundleCycles
