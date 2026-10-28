import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricPELRigidity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexIsogenyDetermination
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricTargetDetermination

/-! # Geometric Composite Determination -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The full actual Tate preimage determines the literal composite datum:
both its geometric moduli target and its marked polarized isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  (hg : D.IsGoodCompletelySplitPrime) (hgeometry : D.HasIntegralModelGeometry)
  {k : Type} [Field k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} {x : D.GeometricPoint b}
  {ts : List (Local.IntegralType s)}

include hg hgeometry in
theorem Data.SphericalPELAlbaneseData.geometricCompositeDatum_eq_of_preimage_eq (a c : D.CompositeDatum x ts)
    (h : Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) a.2.isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) c.2.isogeny.hom) : a = c := by
  have := FiberLattices.charZero_of_field_spec_map b
  rcases a with ⟨y, e⟩
  rcases c with ⟨z, f⟩
  have hy := D.geometricTarget_eq_of_preimage_eq hg hgeometry x y z e f h
  subst z
  have hef : e = f := by
    apply PELIsogenies.PELIsogeny.eq_of_preimage_eq_of_rigid e f D.reference.polarizationType
      (D.fiberPolarizationType hgeometry b x) (D.fiberPolarizationType hgeometry b y)
      hg.2.2.2.2 h
    intro j
    exact D.geometricFiber_abelian_eq_id hgeometry b y j
  exact congrArg (Sigma.mk y) hef

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
