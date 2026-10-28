import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiniteCechModel

/-! # Cohomology Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CohomologyBound

noncomputable section

/-! A finite affine cover bounds genuine quasicoherent cohomology on a compact separated scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem compactSeparated_quasicoherent_cohomology_bounded
    {R : Type u} [CommRing R] {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) [M.IsQuasicoherent] :
    ∃ N, ∀ q, N ≤ q → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj M) := by
  obtain ⟨k, V, ha, _, hcover⟩ := (Line.Bundles.LineBundle.trivial X).exists_finite_affine_frames
  let U : ULift.{u} (Fin k) → X.Opens := fun i => V i.down
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨i, hi⟩ := hcover y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hUa : ∀ i, IsAffineOpen (U i) := fun i => ha i.down
  refine ⟨Fintype.card (ULift.{u} (Fin k)), fun q hq => ?_⟩
  have hz : IsZero ((Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U).X q) :=
    Ordered.CoefficientCechComplex.orderedCoefficientCechObject_isZero_of_card_le c M U q hq
  exact (OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso c M U hU hUa q).isZero_iff.mp
    (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CohomologyBound
