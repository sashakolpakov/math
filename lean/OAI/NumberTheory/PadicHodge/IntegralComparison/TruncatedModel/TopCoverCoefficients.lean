import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelAdditiveTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.LinearCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.SingleGlobalSourceCoefficients

/-! # Top Cover Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverCoefficients

noncomputable section

/-! The literal native top-form coefficient input commutes with the
original linear common-cover comparison. Both coefficient changes
and the ordinary-to-ordered projection remain explicit. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem double_square {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C)
    {S T S' T' : A} {S'' T'' : B} {S''' T''' : C}
    (a : S ⟶ T) (u : S ⟶ S') (v : T ⟶ T') (b : S' ⟶ T')
    (eU : F.obj S' ⟶ S'') (eV : F.obj T' ⟶ T'') (c : S'' ⟶ T'')
    (fU : G.obj S'' ⟶ S''') (fV : G.obj T'' ⟶ T''') (d : S''' ⟶ T''')
    (hp : a ≫ v = u ≫ b) (hF : F.map b ≫ eV = eU ≫ c)
    (hG : G.map c ≫ fV = fU ≫ d) :
    G.map (F.map a) ≫ (G.map (F.map v ≫ eV) ≫ fV) =
      (G.map (F.map u ≫ eU) ≫ fU) ≫ d := by
  calc
    _ = G.map (F.map (a ≫ v) ≫ eV) ≫ fV := by
      simp only [Functor.map_comp, Category.assoc]
    _ = G.map (F.map (u ≫ b) ≫ eV) ≫ fV := by rw [hp]
    _ = G.map (F.map u ≫ eU ≫ c) ≫ fV := by
      apply congrArg (fun w : F.obj S ⟶ T'' => G.map w ≫ fV)
      rw [F.map_comp, Category.assoc, hF]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [hG]

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (g : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev first := OrdinarySectionMap.Ordinary.coefficients p k n
abbrev second := AdditiveTop.Comparison.forget p k
abbrev form := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g
abbrev module := IntrinsicDeRham.TopSingleCoordinates.Intrinsic.module (Truncated.Witt.Ring p k n) X g

local instance form_qc : (form p k n X g).IsQuasicoherent :=
  IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent (Truncated.Witt.Ring p k n) X g

variable {ι κ ν : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → X.left.Opens)

abbrev firstIso := Ordered.SingleGlobalSourceCoefficients.coefficientIso
  (first p k n) (module p k n X g) U g
abbrev secondIso := Ordered.SingleGlobalSourceCoefficients.coefficientIso
  (second p k) (module p k n X g ⋙ first p k n) U g

def inputMap :
    (second p k).obj ((first p k n).obj
      ((ModuleCech.DimensionBound.complex (Truncated.Witt.Ring p k n) X (form p k n X g) U).homology g)) ⟶
    (OrderedCech.Projection.complex U ((module p k n X g ⋙ first p k n) ⋙ second p k)).homology g :=
  (second p k).map ((first p k n).map
      (Module.OrderedCoverCoordinates.projection (Truncated.Witt.Ring p k n) X
        (form p k n X g) U g) ≫ (firstIso p k n X g U).hom) ≫
    (secondIso p k n X g U).hom

omit [Fintype k] [CharP k p] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem small : inputMap p k n X g (AdditiveTopCoordinates.cover p k n X) =
    ModelAdditiveTop.coefficientMorphism p k n X g := rfl

variable (V : κ → X.left.Opens) (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))
  (T : ν → X.left.Opens)
  (rU : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι U)
  (rV : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ V)
  (hT : iSup T = ⊤) (haT : ∀ j, IsAffineOpen (T j))

def coefficientComparison := by
  letI := Module.OrderedCoverCoordinates.ordered_isIso
    (Truncated.Witt.Ring p k n) X (form p k n X g) V T rV hV hT haV haT g
  letI := Ordered.SingleGlobalSourceCoefficients.refinement_isIso
    (first p k n) (module p k n X g) V T rV g
  letI := Ordered.SingleGlobalSourceCoefficients.refinement_isIso
    (second p k) (module p k n X g ⋙ first p k n) V T rV g
  exact Ordered.SingleGlobalSource.coefficientComparison
    ((module p k n X g ⋙ first p k n) ⋙ second p k) g U V T rU rV

omit [Fintype k] [CharP k p] [SmoothOfRelativeDimension g X.hom] in
theorem comparison :
    (second p k).map ((first p k n).map
      (ModuleCech.LinearCover.Comparison.comparison (Truncated.Witt.Ring p k n) X
        (form p k n X g) U V hV haV T rU rV hT haT g)) ≫ inputMap p k n X g V =
    inputMap p k n X g U ≫ coefficientComparison p k n X g U V hV haV T rU rV hT haT := by
  let := Module.OrderedCoverCoordinates.ordered_isIso
    (Truncated.Witt.Ring p k n) X (form p k n X g) V T rV hV hT haV haT g
  let := Ordered.SingleGlobalSourceCoefficients.refinement_isIso
    (first p k n) (module p k n X g) V T rV g
  let := Ordered.SingleGlobalSourceCoefficients.refinement_isIso
    (second p k) (module p k n X g ⋙ first p k n) V T rV g
  exact double_square (first p k n) (second p k) _ _ _ _ _ _ _ _ _ _
    (ModuleCech.LinearCover.Comparison.projection_square (Truncated.Witt.Ring p k n) X
      (form p k n X g) U V hV haV T rU rV hT haT g).symm
    (Ordered.SingleGlobalSourceCoefficients.comparison
      (first p k n) (module p k n X g) U V T rU rV g)
    (Ordered.SingleGlobalSourceCoefficients.comparison
      (second p k) (module p k n X g ⋙ first p k n) U V T rU rV g)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverCoefficients
