import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts

/-! # Immersion Lift Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionLiftFibers

noncomputable section

/-! A lift through a surjective thickening factors uniquely through
any open containing its prescribed restriction. No local coefficient
ring or single-point hypothesis is imposed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {B : Scheme} {S T U Y : Over B} (r : S ⟶ T) [Surjective r.left]
    (i : U ⟶ Y) [IsOpenImmersion i.left] (x : S ⟶ U)

omit [IsOpenImmersion i.left] in
theorem restrictedMorphism_range (f : T ⟶ Y) (hf : r ≫ f = x ≫ i) :
    Set.range f.left ⊆ Set.range i.left := by
  rintro _ ⟨t, rfl⟩
  obtain ⟨s, hs⟩ := (Surjective.surj (f := r.left)) t
  refine ⟨x.left s, ?_⟩
  have h := congrArg (fun g : S.left ⟶ Y.left => g s) (congrArg Over.Hom.left hf)
  exact h.symm.trans (congrArg f.left hs)

def openImmersionLiftFiberEquiv :
    {f : T ⟶ U // r ≫ f = x} ≃ {f : T ⟶ Y // r ≫ f = x ≫ i} where
  toFun f := ⟨f.val ≫ i, (Category.assoc r f.val i).symm.trans (congrArg (fun z => z ≫ i) f.property)⟩
  invFun f := ⟨DualOpen.Lifts.overOpenLift i f.val (restrictedMorphism_range r i x f.val f.property), by
    have : Mono i := Over.mono_of_mono_left i
    apply (cancel_mono i).mp
    rw [Category.assoc, DualOpen.Lifts.overOpenLift_fac, f.property]⟩
  left_inv f := by
    apply Subtype.ext
    have : Mono i := Over.mono_of_mono_left i
    apply (cancel_mono i).mp
    exact DualOpen.Lifts.overOpenLift_fac i (f.val ≫ i) _
  right_inv f := Subtype.ext (DualOpen.Lifts.overOpenLift_fac i f.val _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionLiftFibers
