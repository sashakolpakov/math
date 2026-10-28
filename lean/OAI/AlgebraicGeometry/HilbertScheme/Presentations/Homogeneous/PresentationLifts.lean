import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.PresentationBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LiftedRelationsFlatness

/-! # Presentation Lifts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.PresentationLifts.GradedHilbert

noncomputable section

/-! Flat homogeneous degree quotients lift all specialized relations in that degree; conversely those lifts give tensor exactness. -/

open _root_.MvPolynomial TensorProduct

universe u v z

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
variable {n : ℕ} {ι : Type z} [Fintype ι]

theorem homogeneous_relation_lift_of_flat_quotient
    (hS : Function.Surjective (algebraMap R S))
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ)
    [Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N))]
    (a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing S n) (ha : ∀ i, (a i).IsHomogeneous d)
    (hrel : SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R S) g) a = 0) :
    ∃ b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n, (∀ i, (b i).IsHomogeneous d) ∧
      SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g b = 0 ∧ Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R S) b = a := by
  let f := RelationPresentation.GradedHilbert.homogeneousRelationPresentation g N hg d
  let : Module.Flat R (Hilbert.Polynomial.GradedHilbert.grading R n (d + N) ⧸ f.range) :=
    Module.Flat.of_linearEquiv (RelationPresentation.GradedHilbert.homogeneousPresentationCokernelEquiv g N hg d)
  let a' : ι → Hilbert.Polynomial.GradedHilbert.grading S n d := fun i => ⟨a i, ha i⟩
  let E := PresentationBaseChange.GradedHilbert.homogeneousVectorBaseChangeEquiv (R := R) (S := S) (n := n) (ι := ι) d
  let x := E.symm a'
  have hx : f.lTensor S x = 0 := by
    apply (CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv (R := R) (S := S) (n := n) (d + N)).injective
    rw [LinearEquiv.map_zero, PresentationBaseChange.GradedHilbert.homogeneousPresentation_baseChange]
    change RelationPresentation.GradedHilbert.homogeneousRelationPresentation (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R S) g) N
      (fun i => (hg i).map (algebraMap R S)) d (E (E.symm a')) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext hrel
  obtain ⟨z, hz⟩ := (LiftedRelationsFlatness.lTensor_relations_exact_of_flat_cokernel f S x).mp hx
  obtain ⟨b, rfl⟩ := TensorProduct.mk_surjective (R := R) (M := f.ker) (S := S) hS z
  refine ⟨fun i => (b.val i).val, fun i => (b.val i).property, ?_, ?_⟩
  · exact congrArg Subtype.val b.property
  · have he := congrArg E hz
    change E (f.ker.subtype.lTensor S (1 ⊗ₜ[R] b)) = E x at he
    rw [LinearMap.lTensor_tmul] at he
    change E (1 ⊗ₜ[R] b.val) = E (E.symm a') at he
    rw [LinearEquiv.apply_symm_apply] at he
    funext i
    have hi := congrArg (fun y : ι → Hilbert.Polynomial.GradedHilbert.grading S n d => (y i).val) he
    rw [PresentationBaseChange.GradedHilbert.homogeneousVectorBaseChangeEquiv_tmul, one_smul] at hi
    exact hi

theorem homogeneousPresentation_tensor_exact_of_lifts
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ)
    (hlift : ∀ a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing S n, (∀ i, (a i).IsHomogeneous d) →
      SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R S) g) a = 0 →
      ∃ b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n, (∀ i, (b i).IsHomogeneous d) ∧
        SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g b = 0 ∧ Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R S) b = a) :
    Function.Exact ((RelationPresentation.GradedHilbert.homogeneousRelationPresentation g N hg d).ker.subtype.lTensor S)
      ((RelationPresentation.GradedHilbert.homogeneousRelationPresentation g N hg d).lTensor S) := by
  let f := RelationPresentation.GradedHilbert.homogeneousRelationPresentation g N hg d
  let E := PresentationBaseChange.GradedHilbert.homogeneousVectorBaseChangeEquiv (R := R) (S := S) (n := n) (ι := ι) d
  have hzero : f.comp f.ker.subtype = 0 := by
    apply LinearMap.ext
    intro b
    exact b.property
  intro x
  constructor
  · intro hx
    let a := fun i => (E x i).val
    have ha : SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R S) g) a = 0 := by
      have he := PresentationBaseChange.GradedHilbert.homogeneousPresentation_baseChange (S := S) g N hg d x
      rw [hx, LinearEquiv.map_zero] at he
      exact congrArg Subtype.val he.symm
    obtain ⟨b, hb, hbr, hba⟩ := hlift a (fun i => (E x i).property) ha
    let b' : ι → Hilbert.Polynomial.GradedHilbert.grading R n d := fun i => ⟨b i, hb i⟩
    have hb' : f b' = 0 := Subtype.ext hbr
    refine ⟨1 ⊗ₜ[R] (⟨b', hb'⟩ : f.ker), ?_⟩
    rw [LinearMap.lTensor_tmul]
    apply E.injective
    funext i
    apply Subtype.ext
    rw [PresentationBaseChange.GradedHilbert.homogeneousVectorBaseChangeEquiv_tmul, one_smul]
    exact congrFun hba i
  · rintro ⟨b, rfl⟩
    rw [← LinearMap.lTensor_comp_apply, hzero, LinearMap.lTensor_zero, LinearMap.zero_apply]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.PresentationLifts.GradedHilbert
