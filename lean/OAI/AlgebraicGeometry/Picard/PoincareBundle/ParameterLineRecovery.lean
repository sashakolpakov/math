import OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSquareIsomorphisms

/-! # Parameter Line Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterLineRecovery

noncomputable section

/-! Actual recovery of a coordinate descent restricts to every parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareData
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterKernelFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent

variable {S : Scheme.{u}} {K A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (t : K ⟶ A) (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (M : Line.Bundles.LineBundle (A ⊗ Y).left)
  (r : Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.modulePullbacks)
    (f := fun (_ : PUnit.{1}) => (𝟙 A ⊗ₘ g).left) M.sheaf ≅ Vertical.KernelDescent.ordinaryDatum g L Dv Kv)

/-- The actual restricted quotient line recovers the full parameter-kernel descent. -/
def recovery :
    Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.modulePullbacks)
      (f := fun (_ : PUnit.{1}) => (𝟙 K ⊗ₘ g).left) ((Scheme.Modules.pullback (t ⊗ₘ 𝟙 Y).left).obj M.sheaf) ≅
    Vertical.KernelDescent.ordinaryDatum g (L.pullback (t ⊗ₘ 𝟙 X).left) (Vertical.ParameterKernelFrames.multiplication t L Dv) (Vertical.ParameterKernelFrames.frames t g L Dv Kv) :=
  (DescentSquareIsomorphisms.canonicalIso Geometric.KernelLinearization.modulePullbacks (𝟙 A ⊗ₘ g).left (𝟙 K ⊗ₘ g).left
    (t ⊗ₘ 𝟙 X).left (t ⊗ₘ 𝟙 Y).left (congrArg Over.Hom.left (ParameterSquareData.square t g)) M.sheaf).symm ≪≫
  (DescentSquareIsomorphisms.squareFunctor Geometric.KernelLinearization.modulePullbacks (𝟙 A ⊗ₘ g).left (𝟙 K ⊗ₘ g).left
    (t ⊗ₘ 𝟙 X).left (t ⊗ₘ 𝟙 Y).left (congrArg Over.Hom.left (ParameterSquareData.square t g))).mapIso r ≪≫
  ParameterSquareDescent.iso t g L Dv Kv

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterLineRecovery
