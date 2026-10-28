import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TraceRetraction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.StructureTrace

/-! # Line Trace -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every line bundle on an abelian scheme admits a trace retraction along invertible full-level multiplication. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Abelian.Schemes.AbelianScheme.fullLevel_multiplication_lineBundleUnit_splitMono
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N) (hN : IsUnit (N : Γ(S, ⊤)))
    (L : Line.Bundles.LineBundle A.scheme.left) :
    IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction (A.multiplication N).left).unit.app
      L.sheaf) :=
  LineBundle.TraceRetraction.lineBundle_pullbackUnit_splitMono_of_structureUnit_splitMono (A.multiplication N).left L
    (A.fullLevel_multiplication_structureUnit_splitMono level hN)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
