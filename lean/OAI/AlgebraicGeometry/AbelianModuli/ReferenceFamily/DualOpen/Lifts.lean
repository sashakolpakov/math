import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberSpectrum
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts

noncomputable section

/-! Actual dual-number points lift uniquely through an open immersion
whose source contains their specified reduction point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

def DualSchemePoints (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  {f : LieRanks.dualNumberTest ℂ ⟶ X // LieRanks.dualNumberOrigin ℂ ≫ f = x}

theorem dualSchemePoint_range {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : X ⟶ Y)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (f : DualSchemePoints Y (x ≫ i)) :
    Set.range f.val.left ⊆ Set.range i.left := by
  rintro _ ⟨t, rfl⟩
  let : Surjective (LieRanks.dualNumberOrigin ℂ).left := Dual.NumberSpectrum.dualNumberOrigin_surjective
  obtain ⟨u, hu⟩ := (Surjective.surj (f := (LieRanks.dualNumberOrigin ℂ).left)) t
  refine ⟨x.left u, ?_⟩
  have h := congrArg Over.Hom.left f.property
  have he := congrArg (fun g : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Y.left => g u) h
  change f.val.left ((LieRanks.dualNumberOrigin ℂ).left u) = i.left (x.left u) at he
  exact he.symm.trans (congrArg f.val.left hu)

def overOpenLift {B : Scheme} {X Y Z : Over B} (i : X ⟶ Y) [IsOpenImmersion i.left]
    (f : Z ⟶ Y) (h : Set.range f.left ⊆ Set.range i.left) : Z ⟶ X :=
  Over.homMk (IsOpenImmersion.lift i.left f.left h) (by
    rw [← i.w, ← Category.assoc, IsOpenImmersion.lift_fac, f.w])

theorem overOpenLift_fac {B : Scheme} {X Y Z : Over B} (i : X ⟶ Y) [IsOpenImmersion i.left]
    (f : Z ⟶ Y) (h : Set.range f.left ⊆ Set.range i.left) : overOpenLift i f h ≫ i = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac i.left f.left h

def dualOpenLift {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : X ⟶ Y) [IsOpenImmersion i.left]
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (f : DualSchemePoints Y (x ≫ i)) : DualSchemePoints X x := by
  let l := overOpenLift i f.val (dualSchemePoint_range i x f)
  refine ⟨l, ?_⟩
  apply Over.OverMorphism.ext
  apply (cancel_mono i.left).mp
  have h := congrArg Over.Hom.left ((Category.assoc (LieRanks.dualNumberOrigin ℂ) l i).trans
    ((congrArg (fun g => LieRanks.dualNumberOrigin ℂ ≫ g) (overOpenLift_fac i f.val (dualSchemePoint_range i x f))).trans
      f.property))
  exact h

def dualOpenPointsEquiv {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : X ⟶ Y) [IsOpenImmersion i.left]
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : DualSchemePoints X x ≃ DualSchemePoints Y (x ≫ i) where
  toFun f := ⟨f.val ≫ i, (Category.assoc (LieRanks.dualNumberOrigin ℂ) f.val i).symm.trans
    (congrArg (fun g => g ≫ i) f.property)⟩
  invFun := dualOpenLift i x
  left_inv f := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    apply (cancel_mono i.left).mp
    exact congrArg Over.Hom.left (overOpenLift_fac i (f.val ≫ i) _)
  right_inv f := by
    apply Subtype.ext
    exact overOpenLift_fac i f.val _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts
