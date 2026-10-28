import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.PolarizedDualFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.PolarizationGraphPowerRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosureFieldPullbackEquality

/-! # Test Polarization Graph Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.TestPolarizationGraphRecovery

noncomputable section

/-! On every test scheme of a fixed Noetherian projective abelian family,
a positive graph-bundle power determines a polarization on its chosen dual.
There is no affine, reducedness, or Noetherian restriction on the test. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
variable (T : Over S) (D : Dual.Data.DualAbelianData (A.pullback T.hom)) (p q : PolarizationData.Polarization D δ)
variable (l : (A.pullback T.hom).FullLevel N) (hδ : ∀ i, 0 < δ i)

include PA l hδ in
theorem universalTest_polarization_hom_eq_of_graphPower (d : ℕ) (hd : 0 < d)
    (he : Line.Bundles.LineBundle.classOf (PoincareGraph.Bundles.poincareGraphBundle D p.isogeny.hom) ^ d =
      Line.Bundles.LineBundle.classOf (PoincareGraph.Bundles.poincareGraphBundle D q.isogeny.hom) ^ d) :
    p.isogeny.hom = q.isogeny.hom := by
  let C : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left := ⟨A.pullback T.hom, D, p, l⟩
  apply PolarizedDualFieldDetection.universalPolarizedDual_pointedMap_eq_of_fieldPullbacks A A PA PA T D p l hδ
    p.isogeny.hom q.isogeny.hom (IsMonHom.one_hom _) (IsMonHom.one_hom _)
  exact ClosureFieldPullbackEquality.overHom_fieldPullbacks_eq_of_algClosed p.isogeny.hom q.isogeny.hom
    (C.polarization_graphPower_geometric_recovery hδ q d hd he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.TestPolarizationGraphRecovery
