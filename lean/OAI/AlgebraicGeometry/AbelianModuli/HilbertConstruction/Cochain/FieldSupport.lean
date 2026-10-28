import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.TowerCochainExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HomologySupport

/-! # Field Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.FieldSupport

noncomputable section

/-! An explicit condition on all field-valued coefficient maps controls the homology support of a finite free cochain model and passes to quotient coefficient rings. -/
open _root_.CategoryTheory
universe u
variable {R : Type u} [CommRing R]

def CochainFieldSupport (C : CochainComplex (ModuleCat.{u} R) ℕ) (I : Ideal R) : Prop :=
  ∀ (B : Type u) [Field B] [Algebra R B], ¬ I ≤ RingHom.ker (algebraMap R B) →
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex B C).Acyclic

theorem CochainFieldSupport.quotient
    {C : CochainComplex (ModuleCat.{u} R) ℕ} {I : Ideal R}
    (h : CochainFieldSupport C I) (J : Ideal R) :
    CochainFieldSupport
      (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (R ⧸ J)).mapHomologicalComplex (.up ℕ)).obj C)
      (I.map (Ideal.Quotient.mk J)) := by
  intro B _ _ hnot
  let S := R ⧸ J
  let : Algebra R B := ((algebraMap S B).comp (Ideal.Quotient.mk J)).toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  have hn : ¬ I ≤ RingHom.ker (algebraMap R B) := by
    intro hle
    apply hnot
    apply Ideal.map_le_iff_le_comap.mpr
    exact hle
  intro q
  exact Scalar.TowerCochainExactness.tensor_baseChange_exactAt_of_scalar_tower C q (h B hn q)

theorem CochainFieldSupport.homology_support
    {C : CochainComplex (ModuleCat.{u} R) ℕ} {I : Ideal R}
    (h : CochainFieldSupport C I)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q)) (q : ℕ) :
    Module.support R (C.homology q) ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  apply HomologySupport.finiteFreeCochain_homology_support_of_residue_exactAt C hfin hfree I q
  intro p hp
  apply h p.asIdeal.ResidueField
  simpa only [p.asIdeal.ker_algebraMap_residueField] using hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.FieldSupport
