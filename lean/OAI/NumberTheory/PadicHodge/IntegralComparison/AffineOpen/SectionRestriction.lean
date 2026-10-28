import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameChartMap

/-! # Section Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionRestriction

noncomputable section

/-! Restriction between actual affine-open section algebras gives the native geometric chart map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
  {U V : X.left.Opens} (h : V ≤ U)

def algHom : (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U) →ₐ[k]
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op V) :=
  ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).map (homOfLE h).op).hom

def schemeMap : Spec Γ(X.left, V) ⟶ Spec Γ(X.left, U) :=
  Spec.map (X.left.presheaf.map (homOfLE h).op)

theorem overBase : schemeMap k X h ≫
    (Crystalline.Presentation.affineScheme k ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U))).hom =
    (Crystalline.Presentation.affineScheme k ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op V))).hom :=
  Zero.FrameChartMap.schemeMap_over k _ _ (algHom k X h)

variable (hU : IsAffineOpen U) (hV : IsAffineOpen V)

include hU hV in
theorem factorization : schemeMap k X h ≫ hU.fromSpec = hV.fromSpec :=
  hU.map_fromSpec hV (homOfLE h).op

include hU hV in
theorem openImmersion : IsOpenImmersion (schemeMap k X h) := by
  have : IsOpenImmersion (schemeMap k X h ≫ hU.fromSpec) := (factorization k X h hU hV).symm ▸ inferInstance
  exact IsOpenImmersion.of_comp _ hU.fromSpec

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionRestriction
