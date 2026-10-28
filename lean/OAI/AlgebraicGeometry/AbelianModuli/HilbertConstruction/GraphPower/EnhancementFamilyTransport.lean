import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.FamilyTransport

/-! # Enhancement Family Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower

noncomputable section

/-! Existence of a graph-power-compatible polarization is invariant
under an isomorphism of the underlying group family and a compatible
change of the prescribed line bundle. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {F G : Level.Data.AbelianSchemeWithFullLevel g N S}
variable {L : Line.Bundles.LineBundle F.abelian.scheme.left} {M : Line.Bundles.LineBundle G.abelian.scheme.left} {d : ℕ}

def PolarizationEnhancementData.GraphPowerPolarizationEnhancement.transportFamily (D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d)
    (e : F.abelian.scheme ≅ G.abelian.scheme) [IsMonHom e.hom]
    (he : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf M) = Line.Bundles.LineBundle.classOf L) :
    PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ G M d := by
  let e' : D.object.abelian.scheme ≅ G.abelian.scheme := e
  letI : IsMonHom e'.hom := inferInstanceAs (IsMonHom e.hom)
  let B := D.object.familyTransport (B := G.abelian) e'
  let H := Line.Bundles.LineBundle.pullbackClassMonoidHom e.hom.left
  have hD : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf D.object.graphBundle ^ d := by
    have h : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf (D.object.graphBundle.tensorPower d) :=
      Quotient.sound D.powerIso
    simpa only [Line.Bundles.LineBundle.classOf_tensorPower] using h
  have hB : H (Line.Bundles.LineBundle.classOf B.graphBundle) = Line.Bundles.LineBundle.classOf D.object.graphBundle :=
    (D.object.familyTransportIso (B := G.abelian) e').graphBundle_class
  have hR : H (Line.Bundles.LineBundle.classOf (B.graphBundle.tensorPower d)) =
      Line.Bundles.LineBundle.classOf D.object.graphBundle ^ d := by
    rw [Line.Bundles.LineBundle.classOf_tensorPower, H.map_pow, hB]
  have hM : Line.Bundles.LineBundle.classOf M = Line.Bundles.LineBundle.classOf (B.graphBundle.tensorPower d) := by
    apply (Line.Bundles.LineBundle.pullbackIso ((Over.forget S).mapIso e)).injective
    exact he.trans (hD.trans hR.symm)
  exact ⟨B.dual, B.polarization, Quotient.exact hM⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower
