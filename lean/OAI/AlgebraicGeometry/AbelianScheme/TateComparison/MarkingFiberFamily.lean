import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingAutomorphism
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricFlags

/-! # Marking Fiber Family -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual marking automorphism identifies its geometric fiber
with the scalar marking change of the original fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
  {k : Type} [Field k] (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)

def Data.SphericalPELAlbaneseData.markingFiberFamilyIso (a : (ZMod D.level)ˣ) :
    PELModuli.PELFamilyIso (D.fiberFamily b (x ≫ (D.markingAutomorphism hgeometry a).hom))
      ((D.fiberFamily b x).shiftMarking a) :=
  (D.family.pullbackComp (D.markingAutomorphism hgeometry a).hom.left x.left).symm.trans
    (((D.markingFamilyIso hgeometry a).pullback x.left).trans
      (D.family.shiftMarkingPullbackIso a x.left))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
