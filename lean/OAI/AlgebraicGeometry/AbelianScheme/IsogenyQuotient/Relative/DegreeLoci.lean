import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Degree Loci -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DegreeLoci.Construction

noncomputable section

/-! Finite-flat degree is pulled back from the base when the target
has connected fibres and a section. Its constant-degree loci are open
and closed, without reducedness or Noetherian hypotheses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {X A : Over S} [GrpObj A] [GeometricallyConnected A.hom]
  (f : X ⟶ A) [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left]

def relativeFiniteFlatDegree (s : S) : ℕ := f.left.finrank (η[A].left s)

theorem finiteFlatDegree_eq_base_degree (a : A.left) :
    f.left.finrank a = relativeFiniteFlatDegree f (A.hom a) := by
  apply f.left.isLocallyConstant_finrank.apply_eq_of_isPreconnected
    (A.hom.isConnected_preimage_singleton (A.hom a)).isPreconnected
  · exact Set.mem_singleton _
  · change A.hom (η[A].left (A.hom a)) = A.hom a
    have h := congrArg (fun t : S ⟶ S => t (A.hom a)) η[A].w
    exact h

omit [GeometricallyConnected A.hom] in
theorem relativeFiniteFlatDegree_isLocallyConstant : IsLocallyConstant (relativeFiniteFlatDegree f) :=
  f.left.isLocallyConstant_finrank.comp_continuous η[A].left.continuous

omit [GeometricallyConnected A.hom] in
def relativeDegreeOpen (d : ℕ) : S.Opens :=
  ⟨{s | relativeFiniteFlatDegree f s = d}, (relativeFiniteFlatDegree_isLocallyConstant f).isOpen_fiber d⟩

omit [GeometricallyConnected A.hom] in
theorem relativeDegreeOpen_isClopen (d : ℕ) : IsClopen (relativeDegreeOpen f d : Set S) :=
  (relativeFiniteFlatDegree_isLocallyConstant f).isClopen_fiber d

omit [GeometricallyConnected A.hom] in
theorem mem_relativeDegreeOpen (s : S) : s ∈ relativeDegreeOpen f (relativeFiniteFlatDegree f s) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DegreeLoci.Construction
