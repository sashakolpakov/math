import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ReferenceDatum
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Moduli
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Torsion
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor

/-! # Surface Family -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceFamily.CM

noncomputable section

/-! Construct all deep principal ball surfaces from the full ReferenceFamily
prerequisite and the native admissible reference datum. The lattice is
the actual reference lattice, with no matching-lattice assumption. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

theorem exists_principal_surface_family (hReferenceFamily : Moduli.CM.ReferenceFamilyInput)
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (dref : Fin places.count → Bool) (M : ℕ) (hM : 0 < M) :
    ∃ B' : HeckeCycles.GeometricSource.CM.BallDatum K, B'.b = B.b ∧
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ M ∣ N₀ ∧
        ∀ N : ℕ, 0 < N → N₀ ∣ N → Nonempty (Cm.PrincipalBallSurface K B' N) := by
  obtain ⟨P, hP, hb, hemb, hdist, _⟩ :=
    ReferenceDatum.CM.exists_admissible_reference_datum K B places dref
  have hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice P.lattice := hP.2.2.2.2.2.2.2.2.2.1
  let B' := HeckeCycles.CoverFactor.CM.withLattice K B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2
  have hμ : P.μ = K.val.toRingHom := by
    unfold AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.μ
    rw [hemb, hdist, HeckeCycles.ReferenceDatum.CM.embeddings_distinguished]
  have hι : K.val.toRingHom.comp (RingHom.id K) = P.μ := by
    rw [RingHom.comp_id, hμ]
  obtain ⟨N₀, hN₀, hbase, hlevels⟩ := hReferenceFamily places.count (HeckeCycles.ReferenceDatum.CM.source_degree K places).1
    (HeckeCycles.ReferenceDatum.CM.source_degree K places).2 P hP (RingHom.id K) K.val.toRingHom hι ⊤ M hM
  refine ⟨B', rfl, N₀, hN₀, hbase, ?_⟩
  intro N hN hdiv
  obtain ⟨_, _, Γ, hΓ, _, S, _, _, C₀, X, hX, hunif⟩ := hlevels N hN hdiv
  obtain ⟨π, hπ⟩ := HeckeCycles.ReferenceCover.CM.reference_cover_as_source K B' P hb hμ rfl N X hX.1 Γ hΓ hunif
  exact ⟨Torsion.CM.principalSurfaceOfCover B' N (hN₀.trans (Nat.le_of_dvd hN hdiv)) X π hπ⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceFamily.CM
