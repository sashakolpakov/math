import OAI.NumberTheory.PadicHodge.GeometricComparison.HorizontalHomotopyAt
import OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafTotal

/-! # Horizontal Homotopy Edge -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HorizontalHomotopyEdge.HorizontalHomotopyTotalEdge

noncomputable section

/-! A horizontal contraction of module-presheaf complexes induces the
canonical all-degree quasi-isomorphism to the original total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w
variable (R : Type u) [CommRing R] {D : Type v} [Category.{w} D]
  (M : CochainComplex (D ⥤ ModuleCat.{u} R) ℕ)
  (H : HomologicalComplex₂ (D ⥤ ModuleCat.{u} R) (.up ℕ) (.up ℕ))
  (e : HomotopyEquiv ((CochainComplex.single₀ (CochainComplex (D ⥤ ModuleCat.{u} R) ℕ)).obj M) H)

local instance hasTotal : H.flip.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def edge : M ⟶ H.flip.total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge H.flip) M (fun q => (e.hom.f 0).f q)
    (fun q q' _ => (e.hom.f 0).comm q q') (HorizontalHomotopyAt.HorizontalHomotopyRows.cocycle M H e)

theorem quasiIso : QuasiIso (edge R M H e) :=
  PresheafTotal.PresheafTotalEdge.quasiIso R H.flip M (fun q => (e.hom.f 0).f q)
    (fun q q' _ => (e.hom.f 0).comm q q') (HorizontalHomotopyAt.HorizontalHomotopyRows.cocycle M H e)
    (HorizontalHomotopyAt.HorizontalHomotopyRows.exactAugmentation M H e) (HorizontalHomotopyAt.HorizontalHomotopyRows.mono M H e)
    (HorizontalHomotopyAt.HorizontalHomotopyRows.exactAt M H e)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HorizontalHomotopyEdge.HorizontalHomotopyTotalEdge
