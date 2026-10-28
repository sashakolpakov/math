import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientFixedCover
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ProductProjection
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DiagonalizableQuotientTangentBound

/-! # Coefficient Subgroup Tangent Bound -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientSubgroupTangentBound.Construction

noncomputable section

/-! A singleton diagonalizable subgroup of the target coefficient block
has tangent rank bounded by the original source block's multiplicative height.
The finite flat cover is constructed from the isogeny and its kernel bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TangentRank.CM

variable {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g h : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (hσ : ∀ a, ρ.map a ≫ f.hom = f.hom ≫ σ.map a)
  (τ : Gal(E/ℚ)) (n : ℕ)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ (q ^ n) = 1)
  {d r : ℕ}
  (eA : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp
    q (n + 1) d r)
  (J : Grp (Over (Spec (.of k)))) [IsFinite J.X.hom] [IsCommMonObj J.X] [Subsingleton J.X.left]
  (i : J ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).toGrp)
  [IsClosedImmersion i.hom.hom.left]
  (I : Type) [CommGroup I]
  (iD : J ⟶ (hopfSpec (.of k)).obj (.op (CommHopfAlgCat.of k (MonoidAlgebra k I))))
  [IsClosedImmersion iD.hom.hom.left]

include hf hσ eA i iD in
theorem coefficientSubgroup_tangentRank_le : ∃ t ≤ d, HodgeConjecture.HeckeCycles.TangentRank.CM.HasRank J t := by
  let W := CoefficientFixedCover.Construction.coefficientFixedGroup j iota hsplit A B ρ σ f hσ τ i n
  let p : W ⟶ J := CoefficientFixedCover.Construction.coefficientFixedProjection j iota hsplit A B ρ σ f hσ τ i n
  let u : W ⟶ OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q (n + 1) d ⊗ OrdinaryBlocks.Construction.etaleOrdinaryBlock k q (n + 1) r :=
    CoefficientFixedCover.Construction.coefficientFixedSourceEmbedding j iota hsplit A B ρ σ f hσ τ i n hf ≫ eA.hom
  have : IsFinite W.X.hom := CoefficientFixedCover.Construction.coefficientFixedGroup_finite j iota hsplit A B ρ σ f hσ τ i n hf
  have : IsCommMonObj W.X := CoefficientFixedCover.Construction.coefficientFixedGroup_commutative j iota hsplit A B ρ σ f hσ τ i n hf
  have : IsClosedImmersion (CoefficientFixedCover.Construction.coefficientFixedSourceEmbedding j iota hsplit A B ρ σ f hσ τ i n hf).hom.hom.left :=
    CoefficientFixedCover.Construction.coefficientFixedSourceEmbedding_closed j iota hsplit A B ρ σ f hσ τ i n hf
  have : IsIso eA.hom.hom.hom.left :=
    ((Grp.forget (Over (Spec (.of k)))) ⋙ Over.forget (Spec (.of k))).map_isIso eA.hom
  have : IsClosedImmersion u.hom.hom.left := inferInstanceAs
    (IsClosedImmersion ((CoefficientFixedCover.Construction.coefficientFixedSourceEmbedding j iota hsplit A B ρ σ f hσ τ i n hf).hom.hom.left ≫
      eA.hom.hom.hom.left))
  obtain ⟨hfin, hflat, hfp, _⟩ := CoefficientFixedCover.Construction.coefficientFixedProjection_cover j iota hsplit A B ρ σ f hσ τ i n hf
  let : IsFinite p.hom.hom.left := hfin
  let : Flat p.hom.hom.left := hflat
  let : LocallyOfFinitePresentation p.hom.hom.left := hfp
  have : IsFinite (OrdinaryBlocks.Construction.etaleOrdinaryBlock k q (n + 1) r).X.hom :=
    (OrdinaryBlocks.Construction.etaleOrdinaryBlock_finiteLocallyFree k q (n + 1) r).1
  have : IsSeparated (OrdinaryBlocks.Construction.etaleOrdinaryBlock k q (n + 1) r).X.hom := inferInstance
  let G := ProductProjection.Construction.productProjectionKernel u
  let a : G ⟶ OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q (n + 1) d := ProductProjection.Construction.productProjectionKernelFirst u
  let b : G ⟶ J := ProductProjection.Construction.productProjectionKernelInclusion u ≫ p
  have : IsClosedImmersion a.hom.hom.left := ProductProjection.Construction.productProjectionKernelFirst_closed u
  have : IsFinite G.X.hom := by
    have h : IsFinite ((ProductProjection.Construction.productProjectionKernelInclusion u).hom.hom.left ≫ W.X.hom) :=
      inferInstanceAs (IsFinite
        ((Picard.Homomorphisms.Kernel.Construction.kernelInclusion (u ≫ AnnihilatorSheaf.Construction.splitSecondProjection _ _).hom.hom).left ≫ W.X.hom))
    exact (congrArg IsFinite (ProductProjection.Construction.productProjectionKernelInclusion u).hom.hom.w).mp h
  have : IsCommMonObj G.X := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative (u ≫ AnnihilatorSheaf.Construction.splitSecondProjection _ _).hom.hom
  obtain ⟨_, hbflat, _, hbsurj⟩ := ProductProjection.Construction.productEtaleKernelProjection_cover
    (OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q (n + 1) r) u p
  let : Flat b.hom.hom.left := hbflat
  let : Surjective b.hom.hom.left := hbsurj
  exact DiagonalizableQuotientTangentBound.Construction.diagonalizable_quotient_tangentRank_le G J (OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q (n + 1) d) I
    a iD b (q ^ (n + 1)) d MulEquiv.ulift

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientSubgroupTangentBound.Construction
