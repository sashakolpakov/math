import OAI.NumberTheory.Quaternion.Arithmetic.AdelicOrbitCorrection
import OAI.NumberTheory.Quaternion.Arithmetic.MultiplicativeReduction
import OAI.NumberTheory.Quaternion.Arithmetic.AdelicGroup

/-! # Adelic Compact -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicCompact

noncomputable section

/-! The adelic quotient of a nonsplit quaternion norm-one group is
compact. The compact cover is constructed from short lattice vectors,
finitely many nonzero reduced norms, and explicit orbit reconstruction. -/

open scoped Classical _root_.NumberField _root_.Quaternion
open _root_.NumberField _root_.NumberField.mixedEmbedding Set QuaternionAlgebra

variable {F : Type} [Field F] [NumberField F]

theorem quaternion_nonsplit_compact_adelic_corrections (a b : F) (ha : a ≠ 0)
    (hs : ¬ ∃ x y : F, x ^ 2 - a * y ^ 2 = b) :
    ∃ K : Set (AdelicGroup.FullAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b)), IsCompact K ∧
      ∀ g : AdelicGroup.FullAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b),
        ∃ q : (MatrixGroup.quaternionNormOneMatrixGroup a b).RationalPoints,
          g * AdelicGroup.diagonalFullAdelic (MatrixGroup.quaternionNormOneMatrixGroup a b) q ∈ K := by
  obtain ⟨C, hC, R, hR, hred⟩ := MultiplicativeReduction.quaternion_nonsplit_finite_multiplicative_reduction a b ha hs
  let B (r : ℍ[F,a,b]ˣ) : Set (AdelicGroup.FullAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b)) :=
    (ArchimedeanOrbitCompact.quaternionArchimedeanOrbit a b r ⁻¹' C) ×ˢ
      {g : FiniteAdelicMatrices.FiniteAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b) |
        ∀ v, g v ∈ FiniteOrbitCompact.quaternionFiniteOrbitBox a b r v}
  have hB (r : ℍ[F,a,b]ˣ) : IsCompact (B r) :=
    (ArchimedeanOrbitCompact.quaternionArchimedeanOrbit_compact_preimage a b r C hC).prod
      (FiniteOrbitCompact.quaternion_finite_integral_orbit_isCompact a b r)
  refine ⟨⋃ r ∈ R, B r, hR.isCompact_biUnion (fun r _ => hB r), ?_⟩
  intro g
  obtain ⟨q, r, hr, hx, harch⟩ := hred g.2 g.1
  refine ⟨MatrixGroup.quaternionMatrixPointsEquiv a b (RingHom.id F) q,
    Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, ?_⟩⟩⟩
  constructor
  · change ArchimedeanOrbitCompact.quaternionArchimedeanOrbit a b r
      (g.1 * (MatrixGroup.quaternionNormOneMatrixGroup a b).diagonal Set.univ
        (MatrixGroup.quaternionMatrixPointsEquiv a b (RingHom.id F) q)) ∈ C
    rw [AdelicOrbitCorrection.quaternion_archimedean_orbit_correction]
    exact harch
  · exact AdelicOrbitCorrection.quaternion_finite_orbit_correction a b r q g.2 hx

theorem quaternion_nonsplit_adelic_quotient_compact (a b : F) (ha : a ≠ 0)
    (hs : ¬ ∃ x y : F, x ^ 2 - a * y ^ 2 = b) :
    CompactSpace (AdelicGroup.FullAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b) ⧸
      (AdelicGroup.diagonalFullAdelic (MatrixGroup.quaternionNormOneMatrixGroup a b)).range) := by
  obtain ⟨K, hK, hc⟩ := quaternion_nonsplit_compact_adelic_corrections a b ha hs
  exact AdelicGroup.fullAdelic_quotient_compact_of_corrections (MatrixGroup.quaternionNormOneMatrixGroup a b) K hK hc

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicCompact
