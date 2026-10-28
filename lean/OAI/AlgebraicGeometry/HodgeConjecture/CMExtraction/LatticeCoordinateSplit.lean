import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicCoordinateSplit

/-! # Lattice Coordinate Split -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeCoordinateSplit.TestTransport

noncomputable section

/-! Coordinate-level gluing of three specified lattice membership
predicates, without changing any of the coordinate maps. -/

theorem lattice_coordinate_split {V : Type*} {P Q R A B : Prop}
    (F : V → Prop) {t u : V}
    (hP : P ↔ B) (hs : B ↔ A ∧ F u) (hQ : Q ↔ A) (hR : R ↔ F t)
    (ht : t = u) : P ↔ Q ∧ R :=
  hP.trans (hs.trans (and_congr hQ.symm (hR.trans (Iff.of_eq (congrArg F ht))).symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeCoordinateSplit.TestTransport
