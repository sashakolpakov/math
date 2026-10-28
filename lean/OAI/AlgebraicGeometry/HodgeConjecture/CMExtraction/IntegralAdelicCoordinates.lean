import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalLatticeTopology
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralBasisLattice
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseAdditiveCompletion
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCosets
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Integral Adelic Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralAdelicCoordinates.TestTransport

noncomputable section

section

/-! Extend integral-basis coordinates from the dense rational position
space to its two actual finite-adelic completions. -/

open scoped Classical _root_.NumberField _root_.Topology
open _root_.NumberField OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction Filter

variable (F : Type) [Field F] [NumberField F] (I : Type*) [Fintype I]

def integralPositionCoordinates : (I → F) ≃ₗ[ℚ] ((I × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → ℚ) where
  toFun x ij := (integralBasis F).equivFun (x ij.1) ij.2
  invFun y i := (integralBasis F).equivFun.symm (fun j => y (i, j))
  left_inv x := by funext i; exact (integralBasis F).equivFun.symm_apply_apply (x i)
  right_inv y := by
    funext ij
    exact congr_fun ((integralBasis F).equivFun.apply_symm_apply (fun j => y (ij.1, j))) ij.2
  map_add' x y := by funext ij; simp only [Pi.add_apply, map_add]
  map_smul' c x := by funext ij; simp only [Pi.smul_apply, map_smul, RingHom.id_apply]

def fieldPositionDiagonal : (I → F) →+ (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) where
  toFun := RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition
  map_zero' := by funext i; exact map_zero _
  map_add' x y := by funext i; exact map_add _ _ _

def integralCoordinateDiagonal : (I → F) →+ ((I × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toFun x := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (integralPositionCoordinates F I x)
  map_zero' := by funext i; simp [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal]
  map_add' x y := by funext i; simp [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal]

theorem rationalDiagonal_scaled_integral_iff {J : Type*} (q : ℚ) (hq : q ≠ 0)
    (x : J → ℚ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq ↔ ∀ i, ∃ z : ℤ, q * (z : ℚ) = x i := by
  rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_mem_iff]
  change (∀ i, algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q⁻¹ * algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (x i) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele) ↔ _
  simp only [← map_mul, RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.rational_integral_iff]
  apply forall_congr'
  intro i
  apply exists_congr
  intro z
  constructor
  · intro hz
    rw [hz, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  · intro hz
    rw [← hz, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

omit [Fintype I] in
theorem integralCoordinateDiagonal_lattice_iff (q : ℚ) (hq : q ≠ 0) (x : I → F) :
    integralCoordinateDiagonal F I x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq ↔
      fieldPositionDiagonal F I x ∈ RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (algebraMap ℚ F q)
        ((map_ne_zero (algebraMap ℚ F)).mpr hq) := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (integralPositionCoordinates F I x) ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq ↔
    (fun i => algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (x i)) ∈
      RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (algebraMap ℚ F q) _
  rw [rationalDiagonal_scaled_integral_iff, RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.rational_mem_finiteAdelicPositionLattice_iff]
  change (∀ ij : I × Module.Free.ChooseBasisIndex ℤ (𝓞 F),
    ∃ z : ℤ, q * (z : ℚ) = (integralBasis F).equivFun (x ij.1) ij.2) ↔ _
  simp only [Prod.forall]
  exact forall_congr' (fun i => IntegralBasisLattice.TestTransport.integralBasis_scaled_integral_iff F q (x i))

theorem integralCoordinateDiagonal_nhds :
    comap (fieldPositionDiagonal F I) (𝓝 0) =
      comap (integralCoordinateDiagonal F I) (𝓝 0) := by
  apply Filter.ext
  intro U
  constructor
  · intro hU
    obtain ⟨V, hV, hVU⟩ := mem_comap.mp hU
    obtain ⟨N, hN, hNV⟩ := Finite.LatticeTopology.TestTransport.finitePosition_integer_lattice_nhds F V hV
    have hnQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hW : (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I × Module.Free.ChooseBasisIndex ℤ (𝓞 F))
        (N : ℚ) hnQ).carrier ∈ 𝓝 (0 : (I × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isOpen (ι := I × Module.Free.ChooseBasisIndex ℤ (𝓞 F))
        (N : ℚ) hnQ).mem_nhds (zero_mem _)
    apply mem_of_superset (preimage_mem_comap (m := integralCoordinateDiagonal F I) hW)
    intro x hx
    apply hVU
    apply hNV
    change fieldPositionDiagonal F I x ∈ RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (N : F) _
    simpa only [map_natCast] using (integralCoordinateDiagonal_lattice_iff F I _ hnQ x).mp hx
  · intro hU
    obtain ⟨V, hV, hVU⟩ := mem_comap.mp hU
    obtain ⟨N, hN, hNV⟩ := RationalLatticeTopology.TestTransport.rationalPosition_integer_lattice_nhds V hV
    have hnQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hnF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
    have hW : (RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (ι := I) (N : F) hnF).carrier ∈
        𝓝 (0 : I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
      (RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice_isOpen (ι := I) (N : F) hnF).mem_nhds (zero_mem _)
    apply mem_of_superset (preimage_mem_comap (m := fieldPositionDiagonal F I) hW)
    intro x hx
    change fieldPositionDiagonal F I x ∈ RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (N : F) hnF at hx
    apply hVU
    apply hNV
    apply (integralCoordinateDiagonal_lattice_iff F I _ hnQ x).mpr
    simpa only [map_natCast] using hx

omit [Fintype I] in
theorem integralCoordinateDiagonal_dense : DenseRange (integralCoordinateDiagonal F I) := by
  intro y
  have hr : Set.range (integralCoordinateDiagonal F I) = Set.range RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal := by
    apply Set.ext
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨integralPositionCoordinates F I x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(integralPositionCoordinates F I).symm x,
        congrArg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal ((integralPositionCoordinates F I).apply_symm_apply x)⟩
  rw [hr]
  exact RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.denseRange_finiteDiagonal y

theorem exists_integralAdelicCoordinates :
    ∃ e : (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃ₜ ((I × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf),
      (∀ x, e (fieldPositionDiagonal F I x) = integralCoordinateDiagonal F I x) ∧
      ∀ x y, e (x + y) = e x + e y := by
  let := Finite.LatticeTopology.TestTransport.finiteAdeles_locallyCompact F
  let := Finite.LatticeTopology.TestTransport.finiteAdeles_t2 F
  let : UniformSpace (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) := IsTopologicalAddGroup.rightUniformSpace _
  let : UniformSpace ((I × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
    IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) := isUniformAddGroup_of_addCommGroup
  let : IsUniformAddGroup ((I × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
    isUniformAddGroup_of_addCommGroup
  let : CompleteSpace (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
    IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
  let : CompleteSpace ((I × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
    IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace
      ((I × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
  exact DenseAdditiveCompletion.TestTransport.exists_additive_completion_homeomorph
    (fieldPositionDiagonal F I) (integralCoordinateDiagonal F I)
    RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.denseRange_finiteRationalPosition (integralCoordinateDiagonal_dense F I)
    (integralCoordinateDiagonal_nhds F I)

end

/-! Retain one chosen integral-basis completion map as a continuous
rational linear equivalence. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction

variable (F : Type) [Field F] [NumberField F] (I : Type*) [Fintype I]

instance finiteAdelesRatAlgebra : Algebra ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  ((algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)).comp (algebraMap ℚ F)).toAlgebra

def integralAdelicHomeomorph :
    (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃ₜ ((I × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
  (exists_integralAdelicCoordinates F I).choose

theorem integralAdelicHomeomorph_rational (x : I → F) :
    integralAdelicHomeomorph F I (fieldPositionDiagonal F I x) =
      integralCoordinateDiagonal F I x :=
  (exists_integralAdelicCoordinates F I).choose_spec.1 x

theorem integralAdelicHomeomorph_add (x y : I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    integralAdelicHomeomorph F I (x + y) =
      integralAdelicHomeomorph F I x + integralAdelicHomeomorph F I y :=
  (exists_integralAdelicCoordinates F I).choose_spec.2 x y

def integralAdelicAddEquiv :
    (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃+ ((I × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toEquiv := (integralAdelicHomeomorph F I).toEquiv
  map_add' := integralAdelicHomeomorph_add F I

def integralAdelicLinearEquiv :
    (I → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃L[ℚ] ((I × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toLinearEquiv :=
    { toAddEquiv := integralAdelicAddEquiv F I
      map_smul' := map_rat_smul (integralAdelicAddEquiv F I) }
  continuous_toFun := (integralAdelicHomeomorph F I).continuous
  continuous_invFun := (integralAdelicHomeomorph F I).symm.continuous

theorem integralAdelicLinearEquiv_rational (x : I → F) :
    integralAdelicLinearEquiv F I (fieldPositionDiagonal F I x) =
      integralCoordinateDiagonal F I x := integralAdelicHomeomorph_rational F I x

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralAdelicCoordinates.TestTransport
