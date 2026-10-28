import OAI.NumberTheory.Quaternion.Arithmetic.MinkowskiLocalProjections

/-! # Archimedean Vector Orbit -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ArchimedeanVectorOrbit

noncomputable section

/-! Continuity and compactness transfer for archimedean vector orbits,
stated for an arbitrary matrix group to keep group equations opaque. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField _root_.NumberField.mixedEmbedding Set

variable {F : Type} [Field F] {n : ℕ}

theorem continuous_archimedean_vector_orbit (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (x : Fin n → mixedSpace F) :
    Continuous (fun h : G.ArchimedeanProduct Set.univ =>
      ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val x) := by
  have hc : Continuous (fun h : G.ArchimedeanProduct Set.univ => (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val) :=
    continuous_subtype_val.comp (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G).continuous
  have hm : Continuous (fun h : G.ArchimedeanProduct Set.univ =>
      ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanMixedSL F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val) :=
    (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.continuous_archimedeanMixedSL F n).comp hc
  apply continuous_pi
  intro i
  change Continuous (fun h : G.ArchimedeanProduct Set.univ =>
    ∑ j, ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanMixedSL F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val i j * x j)
  apply continuous_finsetSum
  intro j _
  have hij := (continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply _ hm i)
  exact hij.mul continuous_const

theorem archimedean_vector_orbit_compact_preimage [NumberField F] (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (x : Fin n → mixedSpace F) (C : Set (Fin n → mixedSpace F)) (hC : IsCompact C)
    (hlocal : ∀ v : InfinitePlace F,
      IsCompact {g : G.AtPlace v | g.val.val *ᵥ (fun i => MinkowskiLocalProjections.mixedCompletionProjection v (x i)) ∈
        (fun y : Fin n → mixedSpace F => fun i => MinkowskiLocalProjections.mixedCompletionProjection v (y i)) '' C}) :
    IsCompact {h : G.ArchimedeanProduct Set.univ |
      ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val x ∈ C} := by
  let D (v : (Set.univ : Set (InfinitePlace F))) : Set (G.AtPlace v.val) :=
    {g | g.val.val *ᵥ (fun i => MinkowskiLocalProjections.mixedCompletionProjection v.val (x i)) ∈
      (fun y : Fin n → mixedSpace F => fun i => MinkowskiLocalProjections.mixedCompletionProjection v.val (y i)) '' C}
  have hD (v : (Set.univ : Set (InfinitePlace F))) : IsCompact (D v) := hlocal v.val
  apply (isCompact_univ_pi hD).of_isClosed_subset
    (hC.isClosed.preimage (continuous_archimedean_vector_orbit G x))
  intro h hh v _
  exact ⟨ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val x, hh,
    MinkowskiLocalProjections.mixedCompletionProjection_archimedean_vector _ x v.val⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.ArchimedeanVectorOrbit
