import OAI.ArithmeticGeometry.Models.SpreadingOut.SplitDiagram
import OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteFieldComponents

/-! # Spread Finite Diagram -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SpreadFiniteDiagram.Construction

noncomputable section

/-! The full finite-diagram conclusion of SpreadingOut, with split geometric
components and preserved designated abelian structures. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem spread_finite_diagram_with_abelian_varieties
    (K : Type u) [Field K] [NumberField K]
    {ι α β : Type u} [Fintype ι] [Fintype α] [Fintype β]
    (X : ι → Over (Base.Construction.fieldBase K))
    (hSmooth : ∀ i, Smooth (X i).hom)
    (hProper : ∀ i, IsProper (X i).hom)
    (src dst : α → ι)
    (f : ∀ a, X (src a) ⟶ X (dst a))
    (abelianIndex : β → ι)
    (group : ∀ b, GrpObj (X (abelianIndex b)))
    (hAbelian : ∀ b,
      letI := group b
      IsCommMonObj (X (abelianIndex b)) ∧
        GeometricallyConnected (X (abelianIndex b)).hom) :
    ∃ (E : FiniteFieldComponents.Construction.FiniteNumberFieldExtension K)
      (B : Base.Construction.ArithmeticOpen E.carrier),
      let baseChange :=
        Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap K E.carrier)))
      let genericFiber := Over.pullback B.generic
      ∃ (M : ι → Over B.U.toScheme)
        (fM : ∀ a, M (src a) ⟶ M (dst a))
        (e : ∀ i, genericFiber.obj (M i) ≅ baseChange.obj (X i))
        (groupM : ∀ b, GrpObj (M (abelianIndex b))),
        (∀ i, Smooth (M i).hom ∧ IsProper (M i).hom ∧
          Base.Construction.HasSplitGeometricComponents (M i)) ∧
        (∀ a,
          genericFiber.map (fM a) ≫ (e (dst a)).hom =
            (e (src a)).hom ≫ baseChange.map (f a)) ∧
        (∀ b,
          letI := group b
          letI := groupM b
          letI : GrpObj
              (genericFiber.obj (M (abelianIndex b))) :=
            Functor.grpObjObj (F := genericFiber)
          letI : GrpObj
              (baseChange.obj (X (abelianIndex b))) :=
            Functor.grpObjObj (F := baseChange)
          IsCommMonObj (M (abelianIndex b)) ∧
          GeometricallyConnected (M (abelianIndex b)).hom ∧
          IsMonHom (e (abelianIndex b)).hom) := by
  obtain ⟨E, hsplit⟩ := FiniteFieldComponents.Construction.finite_smooth_proper_components_split_over_number_field K X hSmooth hProper
  let g := Spec.map (CommRingCat.ofHom (algebraMap K E.carrier))
  let F := Over.pullback g
  let Y (i : ι) := F.obj (X i)
  have hsY (i : ι) : Smooth (Y i).hom := by
    have := hSmooth i
    exact inferInstanceAs (Smooth (pullback.snd (X i).hom g))
  have hpY (i : ι) : IsProper (Y i).hom := by
    have := hProper i
    exact inferInstanceAs (IsProper (pullback.snd (X i).hom g))
  let groupY (b : β) : GrpObj (Y (abelianIndex b)) := by
    let := group b
    exact Functor.grpObjObj (F := F)
  have hcommY (b : β) : letI := groupY b; IsCommMonObj (Y (abelianIndex b)) := by
    let := group b
    have := (hAbelian b).1
    exact inferInstanceAs (IsCommMonObj (F.obj (X (abelianIndex b))))
  have hconnY (b : β) : GeometricallyConnected (Y (abelianIndex b)).hom := by
    have := (hAbelian b).2
    exact inferInstanceAs (GeometricallyConnected (pullback.snd (X (abelianIndex b)).hom g))
  obtain ⟨B, M, fM, e, groupM, hM, he, hgroup⟩ :=
    SplitDiagram.Construction.finite_split_group_diagram_arithmetic_model Y hsY hpY hsplit src dst
      (fun a ↦ F.map (f a)) abelianIndex groupY hcommY hconnY
  exact ⟨E, B, M, fM, e, groupM, hM, he, hgroup⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SpreadFiniteDiagram.Construction
