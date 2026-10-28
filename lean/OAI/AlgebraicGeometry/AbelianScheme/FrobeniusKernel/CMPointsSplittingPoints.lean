import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsSplitting

/-! # CM Points Splitting Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsSplittingPoints.Construction

noncomputable section

/-! The constructed native splitting retains its actual point formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))

theorem l45FullTorsionSplitting_inv_points (T : Over S)
    (a : T ⟶ (BlockProducts.Construction.groupBlockProduct s (CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit A ρ n s labels)).X) :
    (A.torsionSchemeYonedaIso (q ^ n)).hom.app (op T)
      (a ≫ (CMPointsSplitting.Construction.l45FullTorsionSplitting j iota hsplit A ρ n s labels).inv.hom.hom) =
        CMPointsSplitting.Construction.l45FullBlockPointsEquiv j iota hsplit A ρ n s labels T a := by
  have h : yonedaGrp.map (CMPointsSplitting.Construction.l45FullTorsionSplitting j iota hsplit A ρ n s labels).inv =
      (CMPointsSplitting.Construction.l45FullBlockPointIso j iota hsplit A ρ n s labels).hom ≫
        (A.torsionSchemeYonedaIso (q ^ n)).inv :=
    (yonedaGrpFullyFaithful (C := Over S)).map_preimage _
  have hp := congrArg (fun f => f.app (op T) a) h
  exact (congrArg ((A.torsionSchemeYonedaIso (q ^ n)).hom.app (op T)) hp).trans
    (((A.torsionSchemeYonedaIso (q ^ n)).app (op T)).inv_hom_id_apply _)

theorem l45FullTorsionSplitting_inv_inclusion (T : Over S)
    (a : T ⟶ (BlockProducts.Construction.groupBlockProduct s (CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit A ρ n s labels)).X) :
    (a ≫ (CMPointsSplitting.Construction.l45FullTorsionSplitting j iota hsplit A ρ n s labels).inv.hom.hom) ≫
        A.torsionInclusion (q ^ n) =
      (CMPointsSplitting.Construction.l45FullBlockPointsEquiv j iota hsplit A ρ n s labels T a).val :=
  congrArg Subtype.val (l45FullTorsionSplitting_inv_points j iota hsplit A ρ n s labels T a)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsSplittingPoints.Construction
