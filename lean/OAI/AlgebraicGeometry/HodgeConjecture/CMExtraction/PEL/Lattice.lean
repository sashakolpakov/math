import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticePadic

/-! # Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.Lattice.TestTransport

noncomputable section

/-! Identify the original PEL completed lattice with the general
completed-vector construction before inspecting its prime coordinates. -/

theorem pel_completed_lattice_eq (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) :
    P.completedLattice = LatticeCoordinates.TestTransport.completedVectorLattice E P.lattice := rfl

theorem norm_coordinates_congr {J V : Type*} [Norm V] (f g : J → V) (h : f = g) :
    (∀ j, ‖f j‖ ≤ 1) ↔ ∀ j, ‖g j‖ ≤ 1 :=
  Iff.of_eq (congrArg (fun z : J → V => ∀ j, ‖z j‖ ≤ 1) h)

theorem membership_iff_of_lattice_eq {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (L M : Submodule R V) (h : L = M) (x : V) {P : Prop} (hP : x ∈ M ↔ P) :
    x ∈ L ↔ P := (Iff.of_eq (congrArg (fun N : Submodule R V => x ∈ N) h)).trans hP

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.Lattice.TestTransport
