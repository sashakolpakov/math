import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.FamilyDimension
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Specialization

/-! # Dimension Specialization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.DimensionSpecialization

noncomputable section

/-! Choose an arithmetic fiber with the same dimension as the specified
complex fiber of a constructed smooth proper group family. The arithmetic
point lies in the image of one actual smooth chart through the identity. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem arithmetic_equal_dimension_specialization
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    (S : Over (Spec (.of K))) [LocallyOfFiniteType S.hom]
    (A : Over S.left) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (c : Spec (.of ℂ) ⟶ S.left) (N : ℕ) (hN : N ≠ 0) :
    ∃ (D : Base.ArithmeticBaseExtension K κ) (p : Over.mk D.fieldExtension ⟶ S),
      D.denominator = N ∧
      topologicalKrullDim ((Over.pullback c).obj A).left =
        topologicalKrullDim ((Over.pullback
          (Spec.map (CommRingCat.ofHom D.embedding) ≫ p.left)).obj A).left := by
  let s := c (IsLocalRing.closedPoint ℂ)
  let x : A.left := η[A].left s
  have hx : A.hom x = s := by
    change (η[A].left ≫ A.hom) s = s
    simp
  obtain ⟨n, U, V, _, _, hxV, e, hn⟩ := SmoothDimensionCharts.DimensionSupport.exists_smoothOfRelativeDimension_chart A.hom x
  let C : Over S.left := Over.mk (V.ι ≫ A.hom)
  let i : C ⟶ A := Over.homMk V.ι
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  have : Smooth C.hom := inferInstanceAs (Smooth (V.ι ≫ A.hom))
  have : SmoothOfRelativeDimension n C.hom := by
    change SmoothOfRelativeDimension n (V.ι ≫ A.hom)
    rw [← Scheme.Hom.resLE_comp_ι A.hom e]
    have : SmoothOfRelativeDimension n (A.hom.resLE U V e) := hn
    exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) (A.hom.resLE U V e ≫ U.ι))
  have hs : s ∈ Set.range C.hom := ⟨⟨x, hxV⟩, hx⟩
  let W : S.left.Opens := ⟨Set.range C.hom, C.hom.isOpenMap.isOpen_range⟩
  let Q : Over (Spec (.of K)) := Over.mk (W.ι ≫ S.hom)
  have : LocallyOfFiniteType Q.hom := inferInstanceAs (LocallyOfFiniteType (W.ι ≫ S.hom))
  have : Nonempty Q.left := ⟨⟨s, hs⟩⟩
  obtain ⟨D, pQ, hD⟩ := Specialization.arithmetic_parameter_exists κ Q N hN
  let j : Q ⟶ S := Over.homMk W.ι
  let p : Over.mk D.fieldExtension ⟶ S := pQ ≫ j
  let t := Spec.map (CommRingCat.ofHom D.embedding) ≫ p.left
  have ht : t (IsLocalRing.closedPoint ℂ) ∈ Set.range C.hom := by
    exact (pQ.left ((Spec.map (CommRingCat.ofHom D.embedding))
      (IsLocalRing.closedPoint ℂ))).property
  refine ⟨D, p, hD, ?_⟩
  exact (Group.FamilyDimension.dimension_algClosed_baseChange_of_smooth_chart A C i n c hs).trans
    (Group.FamilyDimension.dimension_algClosed_baseChange_of_smooth_chart A C i n t ht).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.DimensionSpecialization
