import OAI.ArithmeticGeometry.Models.SpreadingOut.FieldComponentDescent
import OAI.ArithmeticGeometry.Models.SpreadingOut.SplitComponentsBaseChange

/-! # Finite Field Components -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteFieldComponents.Construction

noncomputable section

/-! Finite families of smooth proper schemes acquire split components over
one finite algebraic extension of their field of definition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

def coefficientToField (k L : Type u) [Field k] [Field L] [Algebra k L] (s : Finset L) :
    CoefficientSystem.Constructions.Foundations.coefficientBase k L s ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (CoefficientSystem.Constructions.Foundations.coefficientRing k L s)))

@[reassoc]
theorem coefficientBaseMap_toField
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    {s t : Finset L} (h : s ⊆ t) :
    CoefficientSystem.Constructions.Foundations.coefficientBaseMap k L h ≫ coefficientToField k L s = coefficientToField k L t := by
  unfold CoefficientSystem.Constructions.Foundations.coefficientBaseMap coefficientToField
  erw [← Spec.map_comp]
  congr 1

theorem smooth_proper_components_split_over_coefficient_field
    (k L : Type u) [Field k] [Field L] [IsAlgClosed L]
    [Algebra k L] [Algebra.IsAlgebraic k L]
    (X : Over (Spec (.of k))) [Smooth X.hom] [IsProper X.hom] :
    ∃ s : Finset L,
      Base.Construction.HasSplitGeometricComponents ((Over.pullback (coefficientToField k L s)).obj X) := by
  let c := coefficientToField k L ∅
  let M := (Over.pullback c).obj X
  have : Smooth M.hom := inferInstanceAs (Smooth (pullback.snd X.hom c))
  have : IsProper M.hom := inferInstanceAs (IsProper (pullback.snd X.hom c))
  obtain ⟨j, hj⟩ := FieldComponentDescent.Construction.smooth_proper_components_descend_to_coefficient_field k L ∅ M
  let t := j.left.unop
  let h : ∅ ⊆ t := leOfHom j.hom.unop
  let a := CoefficientSystem.Constructions.Foundations.coefficientBaseMap k L h
  let q := pullback.fst a M.hom
  have hc : a ≫ c = coefficientToField k L t := coefficientBaseMap_toField k L h
  have H : IsPullback (pullback.snd a M.hom ≫ pullback.fst X.hom c) q
      X.hom (coefficientToField k L t) := by
    rw [← hc]
    exact (IsPullback.of_hasPullback a M.hom).flip.paste_horiz
      (IsPullback.of_hasPullback X.hom c)
  let e : (Over.pullback (coefficientToField k L t)).obj X ≅ Over.mk q :=
    Over.isoMk H.isoPullback.symm H.isoPullback_inv_snd
  exact ⟨t, SplitComponentsBaseChange.Construction.hasSplitGeometricComponents_of_iso e hj⟩

theorem split_components_coefficient_enlarge
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (X : Over (Spec (.of k))) {s t : Finset L} (h : s ⊆ t)
    (H : Base.Construction.HasSplitGeometricComponents ((Over.pullback (coefficientToField k L s)).obj X)) :
    Base.Construction.HasSplitGeometricComponents ((Over.pullback (coefficientToField k L t)).obj X) := by
  let a := CoefficientSystem.Constructions.Foundations.coefficientBaseMap k L h
  let c := coefficientToField k L s
  let hc : a ≫ c = coefficientToField k L t := coefficientBaseMap_toField k L h
  let e : Over.pullback (coefficientToField k L t) ≅ Over.pullback c ⋙ Over.pullback a :=
    eqToIso (congrArg (fun z : CoefficientSystem.Constructions.Foundations.coefficientBase k L t ⟶ Spec (.of k) ↦ Over.pullback z) hc.symm) ≪≫ Over.pullbackComp a c
  exact SplitComponentsBaseChange.Construction.hasSplitGeometricComponents_of_iso (e.app X)
    (SplitComponentsBaseChange.Construction.hasSplitGeometricComponents_baseChange a _ H)

theorem finite_smooth_proper_components_split_over_coefficient_field
    (k L : Type u) [Field k] [Field L] [IsAlgClosed L]
    [Algebra k L] [Algebra.IsAlgebraic k L]
    {I : Type*} [Finite I] (X : I → Over (Spec (.of k)))
    (hs : ∀ i, Smooth (X i).hom) (hp : ∀ i, IsProper (X i).hom) :
    ∃ s : Finset L, ∀ i,
      Base.Construction.HasSplitGeometricComponents ((Over.pullback (coefficientToField k L s)).obj (X i)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have H (i : I) := by
    have := hs i
    have := hp i
    exact smooth_proper_components_split_over_coefficient_field k L (X i)
  choose s hs using H
  let t := Finset.univ.biUnion s
  refine ⟨t, fun i ↦ split_components_coefficient_enlarge k L (X i) ?_ (hs i)⟩
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩

/-- The finite extension data used in the frozen SpreadingOut specification. -/
structure FiniteNumberFieldExtension
    (K : Type u) [Field K] [NumberField K] where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra K carrier]
  [finite : FiniteDimensional K carrier]
  [numberField : NumberField carrier]

attribute [instance] FiniteNumberFieldExtension.field FiniteNumberFieldExtension.algebra
  FiniteNumberFieldExtension.finite FiniteNumberFieldExtension.numberField

theorem finite_smooth_proper_components_split_over_number_field
    (K : Type u) [Field K] [NumberField K]
    {I : Type*} [Finite I] (X : I → Over (Spec (.of K)))
    (hs : ∀ i, Smooth (X i).hom) (hp : ∀ i, IsProper (X i).hom) :
    ∃ E : FiniteNumberFieldExtension K, ∀ i,
      Base.Construction.HasSplitGeometricComponents
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K E.carrier)))).obj (X i)) := by
  obtain ⟨s, hs⟩ := finite_smooth_proper_components_split_over_coefficient_field
    K (AlgebraicClosure K) X hs hp
  let F := CoefficientSystem.Constructions.Foundations.coefficientRing K (AlgebraicClosure K) s
  let : Field F := (FieldComponentDescent.Construction.algebraic_coefficient_isField K (AlgebraicClosure K) s).toField
  have : Module.Finite K F := FieldComponentDescent.Construction.algebraic_coefficient_finite K (AlgebraicClosure K) s
  have : NumberField F := NumberField.of_module_finite K F
  exact ⟨⟨F⟩, hs⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteFieldComponents.Construction
