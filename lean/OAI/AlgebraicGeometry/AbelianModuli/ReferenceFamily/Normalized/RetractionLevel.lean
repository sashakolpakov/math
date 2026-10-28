import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.RetractionCarrier
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.PreservationDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.IteratedCarrier
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData

/-! # Retraction Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.RetractionLevel

noncomputable section

/-! A normalized group product preserves the ordered level whenever
the base retraction is surjective. The proof uses actual polarized
pullback isomorphisms and descent of the level labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S T : Scheme.{0}} {g N : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (p : T ⟶ S) (r : S ⟶ T) (w : r ≫ p = 𝟙 S) [Surjective r]
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T)
    (e : A.abelian.scheme ≅ ((A.abelian.pullback r).pullback p).scheme) [IsMonHom e.hom]

theorem normalizedRetraction_level
    (he : NormalizedDual.OpenProductData.NormalizesProductFiber (Over.pullback p) (Over.pullback r) (Pullback.RetractionIso.pullbackRetractionIso p r w) e) :
    A.level.transport (A := A.abelian) (B := (A.abelian.pullback r).pullback p) e =
      (A.level.pullback r).pullback p := by
  let A₀ := A.pullback r
  let B := A₀.pullback p
  let eB := Polarized.IteratedCarrier.polarizedIteratedCarrierIso (X := A.abelian) A r p e
  have : IsMonHom eB.hom := Polarized.IteratedCarrier.polarizedIteratedCarrierIso_isMonHom (X := A.abelian) A r p e
  let j := Polarized.PullbackRetraction.polarizedPullbackRetractionIso A₀ p r w
  have hj : j.abelian.hom = (Pullback.RetractionIso.pullbackRetractionIso p r w).hom.app A₀.abelian.scheme :=
    Polarized.RetractionCarrier.polarizedRetraction_abelian A₀ p r w
  have hi : Level.IsoCalculus.abelianPullbackIso (A := A.abelian) (B := B.abelian) eB r = j.abelian.symm := by
    apply Iso.ext
    apply (cancel_mono j.abelian.hom).mp
    change (Over.pullback r).map eB.hom ≫ j.abelian.hom = j.abelian.inv ≫ j.abelian.hom
    rw [Iso.inv_hom_id, hj]
    exact he
  have h := Level.PreservationDescent.fullLevel_preservation_of_inverse_reduction A B eB r j hi
  have hx := Polarized.IteratedCarrier.polarizedIteratedCarrierIso_transport_heq (X := A.abelian) A r p e A.level
  have hz := Polarized.IteratedCarrier.polarizedIteratedLevel_heq A r p
  exact eq_of_heq (hx.trans ((heq_of_eq h).trans hz))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.RetractionLevel
