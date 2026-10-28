import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.GraphPowerRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.DualTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.FamilyTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FamilyPoincareCompatibility

/-! # Preserves Polarization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A group isomorphism preserving a positive power of the canonical
graph bundle preserves polarization through the canonical dual comparison.
The two objects may have different chosen representing duals. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i)
variable (e : A.abelian.scheme ≅ B.abelian.scheme) [IsMonHom e.hom]
variable (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
variable (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme)

include hδ PB PD PE in
theorem PolarizationData.PolarizedAbelianWithFullLevel.graphPower_preserves_polarization (d : ℕ) (hd : 0 < d)
    (hgraph : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf B.graphBundle ^ d) =
      Line.Bundles.LineBundle.classOf A.graphBundle ^ d) :
    A.polarization.isogeny.hom ≫ (A.dual.familyComparisonIso B.dual e).hom =
      e.hom ≫ B.polarization.isogeny.hom := by
  let F := A.familyTransport (B := B.abelian) e
  let c := A.dual.familyComparisonIso B.dual e
  let : IsMonHom c.hom := A.dual.familyComparisonIso_isMonHom B.dual e PD PE
  have hc : Line.Bundles.LineBundle.pullbackClass (c.hom ⊗ₘ 𝟙 B.abelian.scheme).left
      (Line.Bundles.LineBundle.classOf B.dual.poincare) = Line.Bundles.LineBundle.classOf F.dual.poincare :=
    F.dual.uniqueUnderlyingIso_poincare_class B.dual PB
  let C := F.withDual B.dual c hc
  let H := Line.Bundles.LineBundle.pullbackClassMonoidHom e.hom.left
  have hF : H (Line.Bundles.LineBundle.classOf F.graphBundle) = Line.Bundles.LineBundle.classOf A.graphBundle :=
    (A.familyTransportIso (B := B.abelian) e).graphBundle_class
  have hFB : Line.Bundles.LineBundle.classOf F.graphBundle ^ d = Line.Bundles.LineBundle.classOf B.graphBundle ^ d := by
    apply (Line.Bundles.LineBundle.pullbackIso ((Over.forget S).mapIso e)).injective
    exact ((H.map_pow (Line.Bundles.LineBundle.classOf F.graphBundle) d).trans
      (congrArg (fun z => z ^ d) hF)).trans hgraph.symm
  have hCB : Line.Bundles.LineBundle.classOf C.graphBundle ^ d = Line.Bundles.LineBundle.classOf B.graphBundle ^ d :=
    (congrArg (fun z => z ^ d) (F.withDual_graphBundle_class B.dual c hc)).trans hFB
  have hp : B.polarization.isogeny.hom = C.polarization.isogeny.hom :=
    B.polarization_hom_eq_of_graphPower hδ C.polarization d hd hCB.symm
  rw [hp]
  change A.polarization.isogeny.hom ≫ c.hom =
    e.hom ≫ ((e.inv ≫ A.polarization.isogeny.hom) ≫ c.hom)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
