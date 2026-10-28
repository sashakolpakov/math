import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.DualTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles

/-! # Dual Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A compatible change of representing dual gives a complete
level-preserving moduli isomorphism and preserves the canonical graph
bundle class over the original base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (D : Dual.Data.DualAbelianData A.abelian)
variable (e : A.dual.abelian.scheme ≅ D.abelian.scheme) [IsMonHom e.hom]
variable (he : Line.Bundles.LineBundle.pullbackClass (e.hom ⊗ₘ 𝟙 A.abelian.scheme).left
  (Line.Bundles.LineBundle.classOf D.poincare) = Line.Bundles.LineBundle.classOf A.dual.poincare)

def PolarizationData.PolarizedAbelianWithFullLevel.withDual : PolarizationData.PolarizedAbelianWithFullLevel g δ N S where
  abelian := A.abelian
  dual := D
  polarization := A.polarization.dualTransport e he
  level := A.level

def PolarizationData.PolarizedAbelianWithFullLevel.withDualIso : Moduli.Isomorphisms.LevelPreservingIso A (A.withDual D e he) where
  abelian := Iso.refl A.abelian.scheme
  dual := e
  abelianGroup := by change IsMonHom (𝟙 A.abelian.scheme); infer_instance
  dualGroup := by change IsMonHom e.hom; infer_instance
  polarization := (Category.id_comp _).symm
  poincare := he
  level _ _ := Category.comp_id _

theorem PolarizationData.PolarizedAbelianWithFullLevel.withDual_graphBundle_class :
    Line.Bundles.LineBundle.classOf (A.withDual D e he).graphBundle = Line.Bundles.LineBundle.classOf A.graphBundle := by
  have h := (A.withDualIso D e he).graphBundle_class
  change Line.Bundles.LineBundle.pullbackClass (𝟙 A.abelian.scheme.left)
    (Line.Bundles.LineBundle.classOf (A.withDual D e he).graphBundle) = Line.Bundles.LineBundle.classOf A.graphBundle at h
  rw [Line.Bundles.LineBundle.pullbackClass_id] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
