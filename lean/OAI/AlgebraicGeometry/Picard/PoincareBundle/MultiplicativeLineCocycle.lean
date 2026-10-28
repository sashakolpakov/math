import OAI.AlgebraicGeometry.Picard.PoincareBundle.AssociativeFrameCocycle

/-! # Multiplicative Line Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineCocycle

noncomputable section

/-! Actual line-bundle multiplication determines a normalized cocycle in any normalized frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeFrameCoefficients

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
  (L : Line.Bundles.LineBundle H.left) (D : MultiplicativeLineData.MultiplicativeData L)
  (F : ∀ {T : Over S} (x : T ⟶ H), AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L x)

attribute [local instance] MultiplicativeLineData.MultiplicativeData.product_isIso

/-- The regular multiplication coefficient on the specified test scheme. -/
def value {T : Over S} (a b c : T ⟶ H) (hab : a * b = c) : Γ(T.left, ⊤)ˣ :=
  MultiplicativeFrameCoefficients.coefficient (D.product a b c hab) (F a) (F b) (F c)

/-- Associativity of the given multiplication proves the two-cocycle identity. -/
theorem cocycle {T : Over S} (a b c ab bc d : T ⟶ H)
    (hab : a * b = ab) (hbc : b * c = bc) (had : a * bc = d) (hcd : ab * c = d) :
    value L D F a bc d had * value L D F b c bc hbc =
      value L D F ab c d hcd * value L D F a b ab hab := by
  exact AssociativeFrameCocycle.coefficient_cocycle
    (D.product a b ab hab) (D.product b c bc hbc) (D.product a bc d had) (D.product ab c d hcd)
    (F a) (F b) (F c) (F ab) (F bc) (F d)
    (D.associative a b c ab bc d hab hbc had hcd ⊤)

/-- Normalization of the frame at the identity normalizes the left cocycle value. -/
theorem value_one_left {T : Over S} (a : T ⟶ H) (hF : F (1 : T ⟶ H) = D.unitFrame) :
    value L D F 1 a a (one_mul a) = 1 := by
  apply (Line.FrameUnits.frameRatio_eq_one_iff _ _).mpr
  apply Iso.ext
  apply Line.FrameUnits.unit_hom_ext
  intro U
  rw [Bilinear.ProductFrames.productFrame_app]
  have h := congrArg (fun s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L (1 : T ⟶ H) =>
    (D.product 1 a a (one_mul a)).app U (s.hom.app U (1 : Γ(T.left, U)))
      ((F a).hom.app U (1 : Γ(T.left, U)))) hF
  exact h.trans (D.unit_left a (one_mul a) U ((F a).hom.app U (1 : Γ(T.left, U))))

/-- The same frame normalization gives the right unit law. -/
theorem value_one_right {T : Over S} (a : T ⟶ H) (hF : F (1 : T ⟶ H) = D.unitFrame) :
    value L D F a 1 a (mul_one a) = 1 := by
  apply (Line.FrameUnits.frameRatio_eq_one_iff _ _).mpr
  apply Iso.ext
  apply Line.FrameUnits.unit_hom_ext
  intro U
  rw [Bilinear.ProductFrames.productFrame_app]
  have h := congrArg (fun s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L (1 : T ⟶ H) =>
    (D.product a 1 a (mul_one a)).app U ((F a).hom.app U (1 : Γ(T.left, U)))
      (s.hom.app U (1 : Γ(T.left, U)))) hF
  exact h.trans (D.unit_right a (mul_one a) U ((F a).hom.app U (1 : Γ(T.left, U))))

/-- Commutativity of the actual multiplication gives symmetry of its scalar coefficient. -/
theorem value_symmetric {T : Over S} (a b c : T ⟶ H) (hab : a * b = c) (hba : b * a = c)
    (hcomm : ∀ (U : T.left.Opens) (s : Γ(Line.Fibers.fiber L a, U)) (t : Γ(Line.Fibers.fiber L b, U)),
      (D.product a b c hab).app U s t = (D.product b a c hba).app U t s) :
    value L D F a b c hab = value L D F b a c hba := by
  have hp : Bilinear.ProductFrames.productFrame (D.product a b c hab) (F a) (F b) =
      Bilinear.ProductFrames.productFrame (D.product b a c hba) (F b) (F a) := by
    apply Iso.ext
    apply Line.FrameUnits.unit_hom_ext
    intro U
    rw [Bilinear.ProductFrames.productFrame_app, Bilinear.ProductFrames.productFrame_app]
    exact hcomm U _ _
  exact congrArg (fun p => Line.FrameUnits.frameRatio p (F c)) hp

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineCocycle
