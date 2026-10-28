import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCohomology

/-! # Eta Concrete Homology -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaConcreteHomology.Concrete

noncomputable section

/-!
# The eta formula for categorical homology

The explicit cycle quotients are identified with the homology objects
of the original and eta cochain complexes. Thus the torsion-removal
formula applies to the actual homology functor in every positive degree.
-/

universe u v

open _root_.CategoryTheory OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaComplex OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCycles OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaBoundaries OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCohomology

variable {R : Type u} [CommRing R] (a : R)

def originalHomologyIso (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    C.homology (n + 1) ≅ ModuleCat.of R (EtaCohomology.cohomology C n) :=
  C.homologyIsoSc' n (n + 1) (n + 1 + 1) (by simp) (by simp) ≪≫
    (C.sc' n (n + 1) (n + 1 + 1)).moduleCatHomologyIso

def etaShortComplex (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ModuleCat.ofHom (EtaComplex.differential a C n))
    (ModuleCat.ofHom (EtaComplex.differential a C (n + 1)))
    (ModuleCat.hom_ext (EtaComplex.differential_squared a C n))

def etaShortComplexIso (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    (EtaComplex.eta a C).sc' n (n + 1) (n + 1 + 1) ≅ etaShortComplex a C n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 _ ≫ ModuleCat.ofHom (EtaComplex.differential a C n) = (EtaComplex.eta a C).d n (n + 1) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, EtaComplex.eta_d])
    (by
      change 𝟙 _ ≫ ModuleCat.ofHom (EtaComplex.differential a C (n + 1)) =
        (EtaComplex.eta a C).d (n + 1) (n + 1 + 1) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, EtaComplex.eta_d])

def etaHomologyIso (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    (EtaComplex.eta a C).homology (n + 1) ≅ ModuleCat.of R (EtaCohomology.etaCohomology a C n) :=
  (EtaComplex.eta a C).homologyIsoSc' n (n + 1) (n + 1 + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (etaShortComplexIso a C n) ≪≫
    (etaShortComplex a C n).moduleCatHomologyIso

theorem scalarTorsion_map {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    (EtaCohomology.scalarTorsion a M).map e.toLinearMap = EtaCohomology.scalarTorsion a N := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change a • e y = 0
    have hy' : a • y = 0 := hy
    rw [← map_smul, hy', map_zero]
  · intro hx
    have hx' : a • x = 0 := hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change a • e.symm x = 0
    rw [← map_smul, hx', map_zero]

def torsionQuotientEquiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    (M ⧸ EtaCohomology.scalarTorsion a M) ≃ₗ[R] (N ⧸ EtaCohomology.scalarTorsion a N) :=
  Submodule.Quotient.equiv _ _ e (scalarTorsion_map a e)

def homologyTorsionEquiv (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (ha : IsSMulRegular (C.X (n + 1)) a) (ha' : IsSMulRegular (C.X (n + 1 + 1)) a) :
    (C.homology (n + 1) ⧸ EtaCohomology.scalarTorsion a (C.homology (n + 1))) ≃ₗ[R]
      (EtaComplex.eta a C).homology (n + 1) :=
  (torsionQuotientEquiv a (CategoryTheory.Iso.toLinearEquiv (originalHomologyIso C n))).trans
    ((EtaCohomology.quotientTorsionEquiv a C n ha ha').trans
      (CategoryTheory.Iso.toLinearEquiv (etaHomologyIso a C n)).symm)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaConcreteHomology.Concrete
