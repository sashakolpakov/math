import Mathlib.CategoryTheory.Iso

/-! # Forward Refinement Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ForwardRefinementClass

noncomputable section

/-! Carry a source class forward through a common refinement and
invert the refinement only on the target. -/

open _root_.CategoryTheory

variable {C : Type*} [Category C]
  {P A B T A' B' T' Z : C}
  (xV : P ⟶ A) (xW : P ⟶ B)
  (rV : A ⟶ T) (rW : B ⟶ T)
  (fV : A ⟶ A') (fW : B ⟶ B') (fT : T ⟶ T')
  (rV' : A' ⟶ T') (rW' : B' ⟶ T') [IsIso rW']
  (e : B' ⟶ Z)
  (hsource : xV ≫ rV = xW ≫ rW)
  (hV : fV ≫ rV' = rV ≫ fT) (hW : fW ≫ rW' = rW ≫ fT)

include hsource hV hW in
theorem comparison :
    (xV ≫ fV) ≫ (rV' ≫ inv rW' ≫ e) = (xW ≫ fW) ≫ e := by
  have h : (xV ≫ fV) ≫ rV' = (xW ≫ fW) ≫ rW' := by
    calc
      _ = (xV ≫ rV) ≫ fT := by
        simpa only [Category.assoc] using congrArg (fun z => xV ≫ z) hV
      _ = (xW ≫ rW) ≫ fT := by rw [hsource]
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun z => xW ≫ z) hW.symm
  simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using
    congrArg (fun z => z ≫ inv rW' ≫ e) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ForwardRefinementClass
