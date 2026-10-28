import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.Intrinsic
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CoverCoefficients

/-! # Transported Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.TransportedRefinement

noncomputable section

/-! The transported geometric complementary and common covers satisfy
the source refinement hypotheses on the native principal chart. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover
variable {Y Z : Scheme.{0}} [Y.IsSeparated] (π : Y ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V)
  (hVU : V ≤ π ⁻¹ᵁ U) {m : ℕ} (t : Fin m → Γ(Z,U)) (O : Y.Opens)

abbrev geometric := OpenReindex.geometricOpens π U hU V
abbrev native := Principal.AdditiveSections.opens V hV
abbrev family := PrincipalPoint.Fraction.family U t

variable (hF : ∀ r, IsAffineOpen ((geometric π U hU V).obj r))
  (hpunct : ∀ j, (geometric π U hU V).obj (family U t j) ≤ O)
  (hcover : (geometric π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U)) ⊓ O ≤
    ⨆ j, (geometric π U hU V).obj (family U t j))
  (hglobal : (geometric π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U)) ⊔ O = ⊤)
  {μ : Type} [LinearOrder μ] (A : μ → Y.Opens)
  (hA : iSup A = ⊤) (haA : ∀ j, IsAffineOpen (A j))
  (N : Y.Modules) [N.IsQuasicoherent] (c q : ℕ)

include hVU hF hpunct hcover in
theorem relative_source : IsIso (RelativeCech.Refinement.homology
    ((native V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)))
    (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (geometric π U hU V) (family U t) O)
    (Principal.CanonicalCover.localRight (geometric π U hU V) (family U t) O)
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c) q) := by
  let := Principal.CanonicalRefinement.relative_source (geometric π U hU V) (family U t)
    O hF hpunct hcover N c q
  exact Intrinsic.IntrinsicComparison.native_isIso π U hU V hV hVU
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c) (Principal.CanonicalCover.complementary O)
    (Principal.CanonicalCover.localCover (geometric π U hU V) (family U t) O)
    (Principal.CanonicalCover.localRight (geometric π U hU V) (family U t) O) q

include hF hglobal hA haA in
theorem ordered_source : IsIso (homologyMap (OrderedCech.Refinement.totalMap A
    (Principal.CanonicalCover.globalCover (geometric π U hU V) O A) (Principal.CanonicalCover.globalRight (geometric π U hU V) O A)
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) q) :=
  Principal.CanonicalRefinement.ordered_source (geometric π U hU V) O hF hglobal A hA haA N c q

universe uD vD
variable {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasProducts.{0} D] [HasCoproducts.{0} D]
  (G : AddCommGrpCat.{0} ⥤ D) [G.Additive] [G.PreservesHomology]
  [PreservesLimitsOfSize.{0,0} G]

include hVU hF hpunct hcover in
theorem relative_mapped : IsIso (RelativeCech.Refinement.homology
    ((native V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)))
    (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (geometric π U hU V) (family U t) O)
    (Principal.CanonicalCover.localRight (geometric π U hU V) (family U t) O)
    (Principal.CoefficientHomology.mapped G
      (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) q) := by
  let := relative_source π U hU V hV hVU t O hF hpunct hcover N c q
  exact Presheaf.CoverCoefficients.relative_isIso G
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c)
    ((native V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)))
    (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (geometric π U hU V) (family U t) O)
    (Principal.CanonicalCover.localRight (geometric π U hU V) (family U t) O) q

include hF hglobal hA haA in
theorem ordered_mapped : IsIso (homologyMap (OrderedCech.Refinement.totalMap A
    (Principal.CanonicalCover.globalCover (geometric π U hU V) O A) (Principal.CanonicalCover.globalRight (geometric π U hU V) O A)
    (Principal.CoefficientHomology.mapped G
      (Affine.OrderedInjective.Comparison.sourcePresheaf N c))) q) := by
  let := ordered_source π U hU V O hF hglobal A hA haA N c q
  exact Presheaf.CoverCoefficients.ordered_isIso G
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c)
    A (Principal.CanonicalCover.globalCover (geometric π U hU V) O A) (Principal.CanonicalCover.globalRight (geometric π U hU V) O A) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.TransportedRefinement
