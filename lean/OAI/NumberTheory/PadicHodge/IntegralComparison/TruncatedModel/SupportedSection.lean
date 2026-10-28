import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedRows
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.SupportCover

/-! # Supported Section -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedSection

noncomputable section

/-! The original bounded supported comparison at a section, with
its cover and positive-row exactness supplied by actual geometry. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (U : X.left.affineOpens)
  (s : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X.left)
  [IsClosedImmersion s]

def punctured : Y.left.Opens :=
  AffinePrincipal.SupportCover.outside X.left Y.left f s.ker

variable (g : ℕ) (a : Fin g → Γ(X.left, U.val))
  (ha : Ideal.span (Set.range a) = s.ker.ideal U)

include ha in
omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [IsClosedImmersion s] in
theorem below (i : ULift (Fin g)) :
    (Supported.Comparison.opens p k n X Y f U).obj
      (Supported.Comparison.family p k n X U g a i) ≤
        punctured p k n X Y f s :=
  AffinePrincipal.SupportCover.below X.left U.val U.property Y.left f s.ker a ha i

include ha in
omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [IsClosedImmersion s] in
theorem cover :
    (Supported.Comparison.opens p k n X Y f U).obj
        (⊤_ (PrincipalFrame.Index X.left U)) ⊓ punctured p k n X Y f s ≤
      ⨆ i, (Supported.Comparison.opens p k n X Y f U).obj
        (Supported.Comparison.family p k n X U g a i) :=
  AffinePrincipal.SupportCover.cover X.left U.val U.property Y.left f s.ker a ha

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem global (hs : ⊤ ≤ s ⁻¹ᵁ U.val) :
    (Supported.Comparison.opens p k n X Y f U).obj
        (⊤_ (PrincipalFrame.Index X.left U)) ⊔ punctured p k n X Y f s = ⊤ :=
  AffinePrincipal.SupportCover.section_global X.left U.val U.property Y.left f s hs

variable (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev toBounded (hs : ⊤ ≤ s ⁻¹ᵁ U.val) (i : ℕ) :=
  Supported.Comparison.toBounded p k n X Y f hp U I g a
    (punctured p k n X Y f s) (below p k n X Y f U s g a ha)
    (cover p k n X Y f U s g a ha)
    (SupportedRows.exactAt_succ p k n X Y f U I g a)
    (global p k n X Y f U s hs) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedSection
