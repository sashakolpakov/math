import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactKernels

/-! # Finite Cartier Subgroup Transport -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction

/-!
Concrete chosen subgroups for the ordinary prescriptions. The bundle
retains their actual closed inclusion and finite Cartier coordinates;
it contains no quotient or polarization-descent conclusion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

structure FiniteCartierSubgroup (k : Type) [Field k] (G : Grp (Over (Spec (.of k)))) where
  group : Grp (Over (Spec (.of k)))
  coordinates : CartierModel.Construction.CartierCoordinates (.of k) group
  inclusion : group ⟶ G
  closed : IsClosedImmersion inclusion.hom.hom.left
  finiteLocallyFree : IsFinite group.X.hom ∧ Flat group.X.hom ∧
    LocallyOfFinitePresentation group.X.hom

variable {k : Type} [Field k] {q : ℕ} [Fact q.Prime]

/-- The multiplicative part gives X on the active block and the compact
whole/identity prescription on pure blocks, at every level. -/
def multiplicativeChosenSubgroup {G : Grp (Over (Spec (.of k)))} {n d r : ℕ}
    (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q n d r) : FiniteCartierSubgroup k G where
  group := OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q n d
  coordinates := MultiplicativeDual.Construction.diagonalizableCartierCoordinates k (OrdinaryBlocks.Construction.OrdinaryBlockLabels q n d)
  inclusion := OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e
  closed := OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion_closed k e
  finiteLocallyFree := OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock_finiteLocallyFree k q n d

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (τ : Gal(E/ℚ))
variable (e₁ : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ τ 1) q 1 1 2)

def l45ActiveYChosenSubgroup (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ τ 1) where
  group := EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q L
  coordinates := CMPointsAt.Construction.activeEtaleLineCoordinates L
  inclusion := ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q e₁) L
  closed := ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine_closed k q (ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q e₁) L
  finiteLocallyFree := EtaleSubgroups.Construction.activeEtaleLineScheme_finiteLocallyFree (Spec (.of k)) q L

/-- The source is the q-torsion plane; only its ambient block changes. -/
def l45ActiveZChosenSubgroup :
    FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ τ 2) where
  group := EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q
  coordinates := CMPointsAt.Construction.activeEtalePlaneCoordinates
  inclusion := CMPointsAt.Construction.l45ActivePlaneAtLevelTwo j iota hsplit PEL ρ τ e₁
  closed := CMPointsAt.Construction.l45ActivePlaneAtLevelTwo_closed j iota hsplit PEL ρ τ e₁
  finiteLocallyFree := by
    have : IsFinite (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_finite _ _
    have : Etale (EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_etale _ _
    exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction

namespace AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup

/-! Transport of a chosen finite Cartier subgroup through an ambient
group isomorphism preserves its own scheme and Cartier coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k : Type} [Field k] {G J : Grp (Over (Spec (.of k)))}
variable (H : FiniteCartierSubgroup k G) (e : G ≅ J)

def transport : FiniteCartierSubgroup k J where
  group := H.group
  coordinates := H.coordinates
  inclusion := H.inclusion ≫ e.hom
  closed := by
    have : IsClosedImmersion H.inclusion.hom.hom.left := H.closed
    have : IsIso e.hom.hom.hom.left :=
      inferInstanceAs (IsIso (((Grp.forget _) ⋙ Over.forget _).map e.hom))
    change IsClosedImmersion (H.inclusion.hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  finiteLocallyFree := H.finiteLocallyFree

theorem transport_inclusion :
    (H.transport e).inclusion = H.inclusion ≫ e.hom := rfl

theorem transport_inverse_square :
    (H.transport e).inclusion ≫ e.inv = H.inclusion := by
  change (H.inclusion ≫ e.hom) ≫ e.inv = H.inclusion
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup

end

end OAI
