import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SharedDualMapComparison

/-! # Represented Dual Base Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RepresentedDualBaseChange

noncomputable section

/-! PoincareBundle's actual represented dual map commutes with arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

variable {S T : Scheme.{u}} {a b : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b S}
  (s : T ⟶ S) (f : A.scheme ⟶ B.scheme) [IsMonHom f]
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

/-- Both constructions use the same actual Picard pullback after restriction to the new base. -/
theorem map_dual :
    (Over.pullback s).map (DualMaps.representedDualMap
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f) =
    DualMaps.representedDualMap
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (DA.pullback s)))
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (DB.pullback s))) (AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap s f) := by
  have h1 := congrArg (fun m : DB.abelian.scheme ⟶ DA.abelian.scheme => (Over.pullback s).map m)
    (AbelianScheme.IsogenyQuotient.SharedDualMapComparison.Construction.e45SharedDualMap_eq_native f DA DB)
  have h2 := AbelianScheme.FrobeniusKernel.DualMapBaseChange.Construction.NativePicardPullback.dualMap_baseChange s f DA DB
  have h3 := AbelianScheme.IsogenyQuotient.SharedDualMapComparison.Construction.e45SharedDualMap_eq_native (AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap s f)
    (DA.pullback s) (DB.pullback s)
  exact h1.trans (h2.trans h3.symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RepresentedDualBaseChange
