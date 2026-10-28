import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiFiniteSmoothProper

/-! # Dimensional -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.Dimensional.Comparison

noncomputable section

/-! The dimension-zero base case of the original comparison, stated using the actual topological Krull dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

include f in
theorem finitePoints (hdim : topologicalKrullDim X ≤ 0) : Finite X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsArtinianScheme X := {}
  infer_instance

variable (p ℓ a : ℕ) [Fact p.Prime] [Fact ℓ.Prime] [Fintype k] [CharP k p]
  (hcard : Fintype.card k = p ^ a) [Smooth f]

theorem comparison (hdim : topologicalKrullDim X ≤ 0)
    (hprojective : Projectivity.Construction.ProjectiveOver k f) (i : ℕ) :
    ∃ (hcrys : FiniteDimensional (FractionRing (WittVector p k)) (Interfaces.CrystallineCohomology p k f i))
      (het : FiniteDimensional ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k f i)),
      letI := hcrys
      letI := het
      ∃ P : Polynomial ℤ, P.Monic ∧
        (Interfaces.crystallineQFrobenius p a k hcard f i).charpoly =
          P.map (Int.castRingHom (FractionRing (WittVector p k))) ∧
        (Interfaces.etaleGeometricFrobenius ℓ p a k hcard f i).charpoly = P.map (Int.castRingHom ℚ_[ℓ]) := by
  let : Finite X := finitePoints k f hdim
  exact QuasiFiniteSmoothProper.Comparison.finiteSpace p ℓ a k hcard f hprojective i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.Dimensional.Comparison
