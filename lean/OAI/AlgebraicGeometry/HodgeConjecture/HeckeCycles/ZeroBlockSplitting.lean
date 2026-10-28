import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TrivialGroupIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors

/-! # Zero Block Splitting -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ZeroBlockSplitting.CM

noncomputable section

/-! At torsion level zero the original coefficient block and both
standard factors are the identity group on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction

variable (k : Type) [Field k]

theorem labels_subsingleton (q d : ℕ) : Subsingleton (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q 0 d) := by
  change Subsingleton (ULift (Multiplicative (Fin d → ZMod 1)))
  infer_instance

theorem multiplicative_points (q d : ℕ) (T : Over (Spec (.of k))) :
    Subsingleton (T ⟶ (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 0 d).X) := by
  let : Subsingleton (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q 0 d) := labels_subsingleton q d
  let : Unique (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q 0 d) := uniqueOfSubsingleton 1
  let A := MonoidAlgebra k (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q 0 d)
  let e : A ≃ₐ[k] k := MonoidAlgebra.uniqueAlgEquiv k (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels q 0 d)
  have he : CommRingCat.ofHom (algebraMap k A) = e.symm.toRingEquiv.toCommRingCatIso.hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change (algebraMap k A) a = e.symm a
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using (e.symm.commutes a).symm
  have : IsIso (CommRingCat.ofHom (algebraMap k A)) := by rw [he]; infer_instance
  have : IsIso (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 0 d).X.hom := by
    change IsIso (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    infer_instance
  refine ⟨fun a b => ?_⟩
  apply Over.OverMorphism.ext
  apply (cancel_mono (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 0 d).X.hom).mp
  exact a.w.trans b.w.symm

theorem etale_points (q r : ℕ) (T : Over (Spec (.of k))) :
    Subsingleton (T ⟶ (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 0 r).X) := by
  let : Subsingleton (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q 0 r) := labels_subsingleton q r
  let e := ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of k)) (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q 0 r)).app
    (.op T)).groupIsoToMulEquiv
  refine ⟨fun a b => e.injective ?_⟩
  apply LocallyConstant.ext
  intro t
  exact Subsingleton.elim _ _

theorem product_points (q d r : ℕ) (T : Over (Spec (.of k))) :
    Subsingleton (T ⟶ (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 0 d ⊗ AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 0 r).X) := by
  refine ⟨fun a b => ?_⟩
  apply hom_ext
  · exact (multiplicative_points k q d T).elim _ _
  · exact (etale_points k q r T).elim _ _

variable {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (τ : Gal(E/ℚ))

theorem block_points (T : Over (Spec (.of k))) :
    Subsingleton (T ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 0 τ).X) := by
  let e := PELModuli.CMPoints.BlocksProjectors.splitBlockSchemePointsEquiv j iota hsplit A ρ 0 τ T
  refine ⟨fun a b => e.injective ?_⟩
  apply Subtype.ext
  have ha : (e a).val ^ (q ^ 0) = 1 := (e a).property.1
  have hb : (e b).val ^ (q ^ 0) = 1 := (e b).property.1
  simpa only [pow_zero, pow_one] using ha.trans hb.symm

def splitting (d r : ℕ) : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 0 τ).toGrp q 0 d r :=
  TrivialGroupIso.CM.iso _ _ (block_points j iota hsplit A ρ τ) (product_points k q d r)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ZeroBlockSplitting.CM
