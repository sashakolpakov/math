import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementFamilyTransport

/-! # Enhancement Transport Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower

noncomputable section

/-! Transport of compatible polarization data preserves the complete
moduli object when the group isomorphism also preserves the ordered level. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {F G : Level.Data.AbelianSchemeWithFullLevel g N S}
variable {L : Line.Bundles.LineBundle F.abelian.scheme.left} {M : Line.Bundles.LineBundle G.abelian.scheme.left} {d : ℕ}
variable (D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d)
variable (e : F.abelian.scheme ≅ G.abelian.scheme) [IsMonHom e.hom]
variable (he : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf M) = Line.Bundles.LineBundle.classOf L)
variable (hl : F.level.transport e = G.level)

def PolarizationEnhancementData.GraphPowerPolarizationEnhancement.transportFamilyModuliIso : Moduli.Isomorphisms.LevelPreservingIso D.object (D.transportFamily e he).object := by
  let e' : D.object.abelian.scheme ≅ G.abelian.scheme := e
  letI : IsMonHom e'.hom := inferInstanceAs (IsMonHom e.hom)
  let k := D.object.familyTransportIso (B := G.abelian) e'
  exact {
  abelian := e
  dual := k.dual
  abelianGroup := inferInstanceAs (IsMonHom e.hom)
  dualGroup := k.dualGroup
  polarization := k.polarization
  poincare := k.poincare
  level V labels := congrArg (fun l => (l.hom.app (.op V) labels).val) hl }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower
