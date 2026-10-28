import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELQuotientDetermination
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ModuliUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberPolarizationType
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberLattices

/-! # Geometric Target Determination -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Full Tate preimages determine the actual geometric PEL moduli point.
This uses the constructed complete quotient comparison and fine moduli
uniqueness on the reduced geometric test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  (hg : D.IsGoodCompletelySplitPrime) (hgeometry : D.HasIntegralModelGeometry)
  {k : Type} [Field k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)}

include hg hgeometry in
theorem Data.SphericalPELAlbaneseData.geometricTarget_eq_of_preimage_eq {m : ℕ} (x y z : D.GeometricPoint b)
    (e : PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ m))
    (f : PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b z) (q ^ m))
    (h : Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom) : y = z := by
  have := FiberLattices.charZero_of_field_spec_map b
  have : IsReduced (Over.mk b).left := inferInstanceAs (IsReduced (Spec (.of k)))
  exact D.genericMap_eq_of_familyIso hgeometry y z
    (e.quotientFamilyIsoOfPreimageEq f D.reference.polarizationType
      (D.fiberPolarizationType hgeometry b x) (D.fiberPolarizationType hgeometry b y)
      (D.fiberPolarizationType hgeometry b z) hg.2.2.2.2 h)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
