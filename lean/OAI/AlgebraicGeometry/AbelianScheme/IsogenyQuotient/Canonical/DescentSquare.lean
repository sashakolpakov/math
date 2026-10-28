import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ScalarDescentSymmetry

/-! # Descent Square -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DescentSquare.Construction

noncomputable section

/-! Transporting the actual pullback frame through a square of covers
preserves its canonical descent scalar on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (s : Y' ⟶ Y) (t : X' ⟶ X) (w : t ≫ f = f' ≫ s) (L : Y.Modules)
  (e : (Scheme.Modules.pullback f).obj L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

def canonicalSquareFrame :
    (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback s).obj L) ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X' :=
  (Picard.Homomorphisms.ModuleHomBaseChange.Construction.moduleDescentSquareIso f f' s t w L).symm ≪≫ Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e t

theorem canonicalDescentScalar_square {T : Scheme.{u}} (q : T ⟶ Y') (x y : T ⟶ X')
    (hx : x ≫ f' = q) (hy : y ≫ f' = q) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f' ((Scheme.Modules.pullback s).obj L))
      (canonicalSquareFrame f f' s t w L e) q x y hx hy =
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L) e (q ≫ s) (x ≫ t) (y ≫ t)
      (by rw [Category.assoc, w, ← Category.assoc, hx])
      (by rw [Category.assoc, w, ← Category.assoc, hy]) := by
  let D := (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L
  let b := (Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareComparison f f' s t w).app L
  have hr := CartierDuality.FramedRecovery.Construction.LineDescent.framedDescentScalar_eq_of_recovery
    (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f' ((Scheme.Modules.pullback s).obj L))
    (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f' ((Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareFunctor f f' s t w).obj D))
    ((Picard.Homomorphisms.ModuleHomBaseChange.Construction.nativeDescentEvaluation f').mapIso b.symm) (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e t) q x y hx hy
    (CartierDuality.ScalarDescentSymmetry.Construction.LineDescent.nativeDatumHom_compatible f' _ _ b.inv q x y hx hy)
  exact hr.trans (CartierDuality.FramedBaseChange.Construction.LineDescent.framedDescentScalar_square f f' s t w D e q x y hx hy)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DescentSquare.Construction
