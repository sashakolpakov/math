import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Refinement
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AdditivePullback

/-! # Refined Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.RefinedPullback

noncomputable section

/-! Refined projection and multiplication cocycles retain their
original native H1 pullback classes on an arbitrary common cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : A ⟶ B) {I J : Type}
    (U : I → B.left.Opens) (V : J → A.left.Opens)
    (r : J → I) (hr : ∀ j, V j ≤ f.left ⁻¹ᵁ U (r j))

def regularPairRefinedPullback (v : ∀ i j, Γ(B.left, U i ⊓ U j)) :=
  Refinement.regularPairRefinement A.left (fun i => f.left ⁻¹ᵁ U i) V r hr
    (PairPullback.regularPairPullback f.left U v)

theorem regularPairRefinedPullback_cocycle
    (v : ∀ i j, Γ(B.left, U i ⊓ U j)) (hv : Closed.RegularPairCocycle B.left U v) :
    Closed.RegularPairCocycle A.left V (regularPairRefinedPullback f U V r hr v) :=
  Refinement.regularPairRefinement_cocycle A.left _ V r hr _ (PairPullback.regularPairPullback_cocycle f.left U v hv)

theorem regularPairSheafClass_refinedPullback (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (v : ∀ i j, Γ(B.left, U i ⊓ U j)) (hv : Closed.RegularPairCocycle B.left U v) :
    Closed.regularPairSheafClass A.left V hV (regularPairRefinedPullback f U V r hr v)
      (regularPairRefinedPullback_cocycle f U V r hr v hv) =
      StructurePullback.nativeStructureH1Pullback f (Closed.regularPairSheafClass B.left U hU v hv) :=
  (Refinement.regularPairSheafClass_refinement A.left _ V r hr _
    (Inverse.ImageCechCover.inverseImageCechCover_covers f.left.base U hU) hV
    (PairPullback.regularPairPullback_cocycle f.left U v hv)).trans
      (ClassPullback.regularPairSheafClass_pullback f U hU v hv).symm

local instance refinedPullbackH1Add (Y : Scheme.{0}) :
    AddCommGroup (CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf Y.sheaf) 1) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology Y.carrier) 1 : _ ⥤ AddCommGrpCat.{0}).obj
      (Dual.UnitCechClasses.ringAdditiveSheaf Y.sheaf)))

local instance refinedPullbackH1Module (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule Y.left) 1) := StructureComplexScalars.structureH1ComplexModule Y

theorem regularPairSheafClass_refinedPullback_mul
    {n : ℕ} (G : HilbertConstruction.Abelian.Schemes.AbelianScheme n Foundations.Scheme.ProjectiveSpace.complexBase) (D : HilbertConstruction.Dual.Data.DualAbelianData G)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation G.scheme.left G.scheme.hom)
    {Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType Z.hom] [IsReduced Z.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ Z).left))]
    (a b : Z ⟶ G.scheme) {I J : Type} (U : I → G.scheme.left.Opens) (W : J → Z.left.Opens)
    (hU : iSup U = ⊤) (hW : iSup W = ⊤) (r₀ r₁ r₂ : J → I)
    (h₀ : ∀ j, W j ≤ (a * b).left ⁻¹ᵁ U (r₀ j))
    (h₁ : ∀ j, W j ≤ a.left ⁻¹ᵁ U (r₁ j))
    (h₂ : ∀ j, W j ≤ b.left ⁻¹ᵁ U (r₂ j))
    (v : ∀ i j, Γ(G.scheme.left, U i ⊓ U j)) (hv : Closed.RegularPairCocycle G.scheme.left U v) :
    Closed.regularPairSheafClass Z.left W hW (regularPairRefinedPullback (a * b) U W r₀ h₀ v)
      (regularPairRefinedPullback_cocycle (a * b) U W r₀ h₀ v hv) =
      Closed.regularPairSheafClass Z.left W hW (regularPairRefinedPullback a U W r₁ h₁ v)
        (regularPairRefinedPullback_cocycle a U W r₁ h₁ v hv) +
      Closed.regularPairSheafClass Z.left W hW (regularPairRefinedPullback b U W r₂ h₂ v)
        (regularPairRefinedPullback_cocycle b U W r₂ h₂ v hv) := by
  rw [regularPairSheafClass_refinedPullback (a * b) U W r₀ h₀ hU hW,
    regularPairSheafClass_refinedPullback a U W r₁ h₁ hU hW,
    regularPairSheafClass_refinedPullback b U W r₂ h₂ hU hW]
  exact Intrinsic.AdditivePullback.nativeStructureH1Pullback_mul G D P a b (Closed.regularPairSheafClass G.scheme.left U hU v hv)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.RefinedPullback
