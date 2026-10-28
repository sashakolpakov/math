import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.DescentRecovery

/-! # Product Object -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.ProductObject

noncomputable section

/-!
# Retaining a constructed quotient product with its actual recovery and uniqueness
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
  (hD : Line.Bundles.IsLine (D.obj PUnit.unit)) (M N P : Line.Bundles.LineBundle Y)
  {A B : X.Modules} (eM : (Scheme.Modules.pullback f).obj M.sheaf ≅ A)
  (eN : (Scheme.Modules.pullback f).obj N.sheaf ≅ B)
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A B (D.obj PUnit.unit))
  (hβ : Bilinear.GlobalDescent.Compatible f D M N eM eN β)
  (eP : (Scheme.Modules.pullback f).obj P.sheaf ≅ D.obj PUnit.unit)
  (hP : (Scheme.Modules.pullback (pullback.fst f f)).map eP.hom ≫ (Geometric.CechInvariant.relationGluing f D).hom =
    (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
      pullback.condition).hom.app P.sheaf ≫ (Scheme.Modules.pullback (pullback.snd f f)).map eP.hom)

/-- The constructed product is retained together with its proven exact recovery and uniqueness. -/
def recoveredProduct :
    { δ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M.sheaf N.sheaf P.sheaf //
      ((Scheme.Modules.pullback f).map (Bilinear.BilinearPullback.toHom δ) ≫ eP.hom =
        Bilinear.GlobalDescent.coverMap f D M N eM eN β) ∧
      ∀ ε : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M.sheaf N.sheaf P.sheaf,
        (Scheme.Modules.pullback f).map (Bilinear.BilinearPullback.toHom ε) ≫ eP.hom =
          Bilinear.GlobalDescent.coverMap f D M N eM eN β → ε = δ } := by
  refine ⟨Bilinear.DescentRecovery.descendedBilinear f D hD M N P eM eN β hβ eP hP,
    Bilinear.DescentRecovery.descendedBilinear_fac f D hD M N P eM eN β hβ eP hP, ?_⟩
  intro ε hε
  obtain ⟨δ, _hδ, huniq⟩ := Bilinear.DescentRecovery.existsUnique_bilinear f D hD M N P eM eN β hβ eP hP
  exact (huniq ε hε).trans (huniq _
    (Bilinear.DescentRecovery.descendedBilinear_fac f D hD M N P eM eN β hβ eP hP)).symm

/-- The retained product is exactly the original genuine descent construction. -/
theorem recoveredProduct_val : (recoveredProduct f D hD M N P eM eN β hβ eP hP).val =
    Bilinear.DescentRecovery.descendedBilinear f D hD M N P eM eN β hβ eP hP := rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.ProductObject
