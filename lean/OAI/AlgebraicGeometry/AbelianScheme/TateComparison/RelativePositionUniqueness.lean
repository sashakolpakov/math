import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality

/-! # Relative Position Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionUniqueness

noncomputable section

/-! The supplied elementary-divisor uniqueness makes the ordinary
relative-position exponents intrinsic to the two actual lattices. -/

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem relativePosition_exponents_unique (hElementaryDivisors : Duality.ElementaryDivisorsInput R K) (π : R) (hπ : Irreducible π)
    (L M : Duality.RankThreeLattice R K) (a b : Fin 3 → ℤ) (ha : Antitone a) (hb : Antitone b)
    (hA : Duality.RelativePosition π a L M) (hB : Duality.RelativePosition π b L M) : a = b := by
  obtain ⟨c, _, hc⟩ := hElementaryDivisors π hπ L.val M.val L.property M.property
  have hca : (fun i => -a i) = c := hc _ ⟨fun _ _ hij => neg_le_neg (ha hij), hA⟩
  have hcb : (fun i => -b i) = c := hc _ ⟨fun _ _ hij => neg_le_neg (hb hij), hB⟩
  funext i
  exact neg_inj.mp (congrFun (hca.trans hcb.symm) i)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionUniqueness
