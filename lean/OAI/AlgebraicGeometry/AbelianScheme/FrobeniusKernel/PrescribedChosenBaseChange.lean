import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedBlockBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockComponents

/-! # Prescribed Chosen Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedChosenBaseChange.Construction

noncomputable section

/-! Original chosen points commute with native block base change,
retaining the square of their actual subgroup inclusions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k k' : Type} [Field k] [Field k'] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (s : Spec (.of k') ⟶ Spec (.of k)) (n : ℕ) (τ : Gal(E/ℚ))

theorem canonicalOriginalBlockPoint_baseChange (Q : Over (Spec (.of k')))
    (z : Q ⟶ (Over.pullback s).obj (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X) :
    A.abelian.torsionBaseChangeEquiv s Q (q ^ n)
      (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit (A.pullback s) (ρ.pullback s) n τ Q
        (z ≫ (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A.abelian ρ s n τ).hom.hom.hom)) =
      CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ ((Over.map s).obj Q)
        (((Over.mapPullbackAdj s).homEquiv Q (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X).symm z) := by
  apply Subtype.ext
  have h := congrArg (fun a : PELModuli.CMPoints.BlocksProjectors.blockPoints A.abelian ρ (j.localCharacter iota τ) n
    ((Over.map s).obj Q) => a.val)
      (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso_blockPoints j iota hsplit A.abelian ρ s n τ Q z)
  exact h

variable (H : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
variable (H' : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k'
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit (A.pullback s) (ρ.pullback s) τ n))
variable (l : (Over.pullback s).obj H.group.X ⟶ H'.group.X)
variable (hl : l ≫ H'.inclusion.hom.hom = (Over.pullback s).map H.inclusion.hom.hom ≫
  (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A.abelian ρ s n τ).hom.hom.hom)

include hl in
theorem prescribedChosenPoint_baseChange (Q : Over (Spec (.of k')))
    (z : Q ⟶ (Over.pullback s).obj H.group.X) :
    A.abelian.torsionBaseChangeEquiv s Q (q ^ n)
      (Prescription.Construction.prescribedChosenPoint j iota hsplit (A.pullback s) (ρ.pullback s) n τ H' Q (z ≫ l)) =
      Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H ((Over.map s).obj Q)
        (((Over.mapPullbackAdj s).homEquiv Q H.group.X).symm z) := by
  have hs := (Category.assoc z l H'.inclusion.hom.hom).trans
    ((congrArg (fun a => z ≫ a) hl).trans (Category.assoc z
      ((Over.pullback s).map H.inclusion.hom.hom) _).symm)
  have hleft := congrArg (fun a => A.abelian.torsionBaseChangeEquiv s Q (q ^ n)
    (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit (A.pullback s) (ρ.pullback s) n τ Q a)) hs
  have hb := canonicalOriginalBlockPoint_baseChange j iota hsplit A ρ s n τ Q
    (z ≫ (Over.pullback s).map H.inclusion.hom.hom)
  have hp := (Over.mapPullbackAdj s).homEquiv_naturality_right_symm z H.inclusion.hom.hom
  exact hleft.trans (hb.trans (congrArg
    (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ ((Over.map s).obj Q)) hp))

omit l hl in
theorem prescribedChosenPoint_baseChange_iso
    (e : (Over.pullback s).obj H.group.X ≅ H'.group.X)
    (he : e.hom ≫ H'.inclusion.hom.hom = (Over.pullback s).map H.inclusion.hom.hom ≫
      (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A.abelian ρ s n τ).hom.hom.hom)
    (Q : Over (Spec (.of k'))) (z : Q ⟶ H'.group.X) :
    A.abelian.torsionBaseChangeEquiv s Q (q ^ n)
      (Prescription.Construction.prescribedChosenPoint j iota hsplit (A.pullback s) (ρ.pullback s) n τ H' Q z) =
      Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H ((Over.map s).obj Q)
        (((Over.mapPullbackAdj s).homEquiv Q H.group.X).symm (z ≫ e.inv)) := by
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    prescribedChosenPoint_baseChange j iota hsplit A ρ s n τ H H' e.hom he Q (z ≫ e.inv)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedChosenBaseChange.Construction
