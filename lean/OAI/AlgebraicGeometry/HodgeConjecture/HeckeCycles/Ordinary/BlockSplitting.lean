import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCharacters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralSubgroup
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralCharacterEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupTensorIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleGroupFunctor
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeBlockFlatness

/-! # Block Splitting -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.BlockSplitting.CM

noncomputable section

/-! Transfer the constructed ambient multiplicative factor to each
original coefficient block. The factor dimensions are constructed;
the height and Lie signature identify them. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [IsAlgClosed k] [CharP k q] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

theorem exists_splitting_of_multiplicative_torsion
    (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ) (τ : Gal(E/ℚ))
    (hambient :
      letI : IsFinite (A.abelian.torsionScheme (q ^ (n + 1))).hom :=
        TorsionFinite.CM.torsion_finite A.abelian q hordinary (n + 1)
      Nonempty (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart (PELModuli.CMPoints.BlockRetraction.actualTorsionGroup (q := q) A.abelian (n + 1)) ≅
        AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q (n + 1) g)) :
    ∃ d r : ℕ, Nonempty (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A.abelian ρ (n + 1) τ).toGrp q (n + 1) d r) := by
  let : IsFinite (A.abelian.torsionScheme (q ^ (n + 1))).hom :=
    TorsionFinite.CM.torsion_finite A.abelian q hordinary (n + 1)
  let Tor := PELModuli.CMPoints.BlockRetraction.actualTorsionGroup (q := q) A.abelian (n + 1)
  let B := (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A.abelian ρ (n + 1) τ).toGrp
  let : IsFinite Tor.X.hom := TorsionFinite.CM.torsion_finite A.abelian q hordinary (n + 1)
  let : IsFinite B.X.hom := PELModuli.CMPoints.FiniteGroupPresentation.idempotentBlock_finite A.abelian ρ (q ^ (n + 1))
    (j.projector iota hsplit (n + 1) τ)
  let : IsCommMonObj Tor.X := A.abelian.torsionScheme_commutative (q ^ (n + 1))
  let : IsCommMonObj B.X := (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A.abelian ρ (n + 1) τ).comm
  let inc : B ⟶ Tor := PELModuli.CMPoints.BlockRetraction.blockToTorsionGroup j iota hsplit A.abelian ρ (n + 1) τ
  let : IsClosedImmersion inc.hom.hom.left :=
    PELModuli.CMPoints.BlockRetraction.blockToTorsionGroup_closed j iota hsplit A.abelian ρ (n + 1) τ
  let pr : Tor ⟶ B := PELModuli.CMPoints.BlockRetraction.torsionToBlockGroup j iota hsplit A.abelian ρ (n + 1) τ
  have hret : inc.hom.hom ≫ pr.hom.hom = 𝟙 B.X :=
    PELModuli.CMPoints.BlockRetraction.block_scheme_retraction j iota hsplit A.abelian ρ (n + 1) τ
  let : Mono inc.hom.hom := mono_of_mono_fac hret
  obtain ⟨ea⟩ := hambient
  obtain ⟨R, hR, ⟨iR⟩, hspan⟩ := NeutralSubgroup.CM.spanning_presentation Tor B inc
    (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q (n + 1) g) ea
  let : Module.Finite k R := hR
  obtain ⟨d, ⟨ec⟩⟩ := BlockCoordinates.CM.character_coordinates j iota hsplit A ρ hordinary n τ
  obtain ⟨r, ⟨ep⟩⟩ := BlockCoordinates.CM.points_coordinates j iota hsplit A.abelian ρ hordinary n τ
  have hkill : ∀ p : Over.mk (𝟙 (Spec (.of k))) ⟶ B.X, p ^ (q ^ (n + 1)) = 1 :=
    TorsionCharacters.CM.subgroup_points_killed A.abelian (q ^ (n + 1)) B inc
      (Over.mk (𝟙 (Spec (.of k))))
  let c := (NeutralCharacterEquiv.CM.characterEquiv B q (n + 1) hkill).symm.trans ec
  let im := DiagonalizableCoordinates.CM.multiplicativeIso (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart B) R iR hspan q (n + 1) d c
  let u : TorsionCoordinateMaps.CM.Criterion.coordinates q (n + 1) r ≃* AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q (n + 1) r := MulEquiv.ulift.symm
  let it : HeckeCycles.Finite.GroupDecomposition.CM.pointGroup B ≅ AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.etaleOrdinaryBlock k q (n + 1) r :=
    AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupIso (Spec (.of k)) (ep.trans u)
  exact ⟨d, r, ⟨(HeckeCycles.Finite.GroupDecomposition.CM.decomposition B).symm ≪≫
    GroupTensorIso.CM.left (HeckeCycles.Finite.GroupDecomposition.CM.pointGroup B) (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart B) (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q (n + 1) d) im ≪≫
    GroupTensorIso.CM.right (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q (n + 1) d)
      (HeckeCycles.Finite.GroupDecomposition.CM.pointGroup B) (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.etaleOrdinaryBlock k q (n + 1) r) it⟩⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.BlockSplitting.CM
