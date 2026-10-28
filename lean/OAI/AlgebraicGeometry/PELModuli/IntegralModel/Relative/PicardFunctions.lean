import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeFunctionsIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatBase
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ProductOpenCover
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

/-! # Picard Functions -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PicardFunctions.RelativePicardFunctions

noncomputable section

/-! Functions on an abelian family over a reduced noetherian parameter
come from the parameter. The same comparison holds on every flat
parameter change, including nonreduced covers and their Cech overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (T : Over S) [IsReduced T.left] [IsNoetherian T.left]

theorem product_isReduced : IsReduced (T ⊗ A.scheme).left := by
  let π := (fst T A.scheme).left
  have : Smooth π := inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.fst T.hom A.scheme.hom))
  have : GeometricallyReduced π := Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.geometricallyReduced_of_smooth π
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian π

omit [IsReduced T.left] in
theorem product_isNoetherian : IsNoetherian (T ⊗ A.scheme).left := by
  let π := (fst T A.scheme).left
  have : LocallyOfFiniteType π :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.fst T.hom A.scheme.hom))
  have : QuasiCompact π :=
    inferInstanceAs (QuasiCompact (CategoryTheory.Limits.pullback.fst T.hom A.scheme.hom))
  let : IsLocallyNoetherian (T ⊗ A.scheme).left := LocallyOfFiniteType.isLocallyNoetherian π
  let : CompactSpace (T ⊗ A.scheme).left := QuasiCompact.compactSpace_of_compactSpace π
  exact ⟨⟩

theorem isIso_product_app (U : T.left.Opens) : IsIso ((fst T A.scheme).left.app U) := by
  let : IsReduced (T ⊗ A.scheme).left := product_isReduced A T
  have : IsProper (fst T A.scheme).left :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.fst T.hom A.scheme.hom))
  have : Smooth (fst T A.scheme).left :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.fst T.hom A.scheme.hom))
  have : GeometricallyConnected (fst T A.scheme).left :=
    inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.fst T.hom A.scheme.hom))
  exact Quotients.FiniteDescent.RelativeFunctionsIs.Construction.RelativeFunctions.isIso_app (fst T A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A T) U

theorem isIso_flat_product_app {V : Over S} (v : V ⟶ T) [Flat v.left] (U : V.left.Opens) :
    IsIso ((fst V A.scheme).left.app U) := by
  let : IsNoetherian (T ⊗ A.scheme).left := product_isNoetherian A T
  exact Quotients.FiniteDescent.FlatBase.Construction.FlatBaseChangeFunctions.isIso_app (fst T A.scheme).left v.left
    (v ▷ A.scheme).left (fst V A.scheme).left
    (Picard.ProductOpenCover.PicardProductOpenCover.productMap_isPullback A.scheme v) (isIso_product_app A T) U

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PicardFunctions.RelativePicardFunctions
