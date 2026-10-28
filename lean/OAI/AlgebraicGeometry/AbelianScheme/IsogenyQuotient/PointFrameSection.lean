import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberProductOrigin

/-! # Point Frame Section -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PointFrameSection.Construction

noncomputable section

/-! The frame of a global pullback at a point is exactly the native
pulled section with its geometric fiber comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

universe u

theorem atPoint_hom_eq_pullSection {S : Scheme.{u}} {A B T : Over S}
    (f : A ⟶ B) (L : Picard.PoincareBundle.Line.Bundles.LineBundle B.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L f)
    (x : T ⟶ A) (q : T ⟶ B) (hx : x ≫ f = q) :
    (Picard.PoincareBundle.GlobalPullbackFrame.atPoint f L s x q hx).hom = Picard.PoincareBundle.Line.Fibers.pullSection L x f q hx s.hom := by
  unfold Picard.PoincareBundle.GlobalPullbackFrame.atPoint Picard.PoincareBundle.Line.Fibers.pullSection
  rw [FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison]
  rfl

theorem atPoint_eq_of_pulled_section {S : Scheme.{u}} {A B T : Over S}
    (f : A ⟶ B) (L : Picard.PoincareBundle.Line.Bundles.LineBundle B.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L f)
    (x : T ⟶ A) (q : T ⟶ B) (hx : x ≫ f = q)
    (v : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L q)
    (hv : Picard.PoincareBundle.Line.Fibers.pullSection L x f q hx s.hom = v.hom) : Picard.PoincareBundle.GlobalPullbackFrame.atPoint f L s x q hx = v :=
  Iso.ext ((atPoint_hom_eq_pullSection f L s x q hx).trans hv)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PointFrameSection.Construction
