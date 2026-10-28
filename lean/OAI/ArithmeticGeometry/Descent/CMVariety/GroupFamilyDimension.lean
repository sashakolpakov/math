import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.FamilyDimension

/-! # Group Family Dimension -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.GroupFamilyDimension.Abelian

noncomputable section

/-! A dominant algebraically closed fiber fixes the relative dimension
of a smooth proper geometrically connected group family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.FamilyDimension

theorem smooth_group_dimension_of_dominant_fiber
    {S : Scheme} (M : Over S) [GrpObj M] [IsCommMonObj M]
    [Smooth M.hom] [IsProper M.hom] [GeometricallyConnected M.hom]
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S) [IsDominant t]
    (g : ℕ) (hg : topologicalKrullDim ((Over.pullback t).obj M).left = (g : WithBot ℕ∞)) :
    SmoothOfRelativeDimension g M.hom := by
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth M.hom x
  let : Algebra Γ(S, U) Γ(M.left, V) := (M.hom.appLE U V e).hom.toAlgebra
  change Algebra.IsStandardSmooth Γ(S, U) Γ(M.left, V) at hstd
  obtain ⟨indices, relations, hrelations, hindices, ⟨Q⟩⟩ := hstd
  let := hrelations
  let := hindices
  have hQ := Q.isStandardSmoothOfRelativeDimension rfl
  have : SmoothOfRelativeDimension Q.dimension (M.hom.resLE U V e) :=
    AlgebraicGeometry.PELModuli.IntegralModel.SmoothDimensionCharts.DimensionSupport.smoothOfRelativeDimension_resLE_of_appLE M.hom Q.dimension U V hU hV e hQ
  let C : Over S := Over.mk (V.ι ≫ M.hom)
  let i : C ⟶ M := Over.homMk V.ι
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  have : Nonempty C.left := ⟨⟨x, hx⟩⟩
  have : SmoothOfRelativeDimension Q.dimension C.hom := by
    change SmoothOfRelativeDimension Q.dimension (V.ι ≫ M.hom)
    rw [← Scheme.Hom.resLE_comp_ι M.hom e]
    exact inferInstanceAs (SmoothOfRelativeDimension (Q.dimension + 0) (M.hom.resLE U V e ≫ U.ι))
  have : Smooth C.hom := SmoothOfRelativeDimension.smooth Q.dimension C.hom
  have ht : t (IsLocalRing.closedPoint K) ∈ Set.range C.hom := by
    obtain ⟨b, hb, p, hp⟩ := t.denseRange.inter_open_nonempty (Set.range C.hom)
      C.hom.isOpenMap.isOpen_range (Set.range_nonempty C.hom)
    rw [← hp, Subsingleton.elim p (IsLocalRing.closedPoint K)] at hb
    exact hb
  have hn : Q.dimension = g := by
    exact_mod_cast (AlgebraicGeometry.PELModuli.IntegralModel.Group.FamilyDimension.dimension_algClosed_baseChange_of_smooth_chart M C i Q.dimension t ht).symm.trans hg
  exact ⟨U, hU, V, hV, hx, e, hn ▸ hQ⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.GroupFamilyDimension.Abelian
