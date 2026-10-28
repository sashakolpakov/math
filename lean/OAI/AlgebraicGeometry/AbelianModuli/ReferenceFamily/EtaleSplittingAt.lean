import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Etale Splitting At -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting

noncomputable section

/-! Finite etale algebras give constructed splitting covers of their
actual affine schemes. No global torsion trivialization is supplied. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def affineOver : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))

def affineAlgIso {C : Type} [CommRing C] [Algebra R C] (e : B ≃ₐ[R] C) :
    affineOver R C ≅ affineOver R B :=
  Over.isoMk (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op) (by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap R C))
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun r => e.commutes r))

def constantAffineIso (n : ℕ) :
    HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of R)) (Fin n) ≅ affineOver R (Fin n → R) := by
  let e : (∐ fun _ : Fin n => Spec (.of R)) ≅ Spec (.of (Fin n → R)) :=
    asIso (sigmaSpec (fun _ : Fin n => CommRingCat.of R))
  refine Over.isoMk e ?_
  apply Sigma.hom_ext
  intro i
  change Sigma.ι _ i ≫ sigmaSpec (fun _ : Fin n => CommRingCat.of R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Fin n → R))) =
      Sigma.ι _ i ≫ Sigma.desc (fun _ : Fin n => 𝟙 (Spec (.of R)))
  rw [ι_sigmaSpec_assoc, Sigma.ι_comp_desc, ← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap R (Fin n → R)) ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => R) i) = 𝟙 _ := by
    ext r
    rfl
  rw [h, Spec.map_id]

variable (T : Type) [CommRing T] [Algebra R T]

def affineBaseChangeIso : affineOver T (T ⊗[R] B) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))).obj (affineOver R B) :=
  Over.isoMk ((pullbackSpecIso R T B).symm ≪≫ pullbackSymmetry _ _) (by
    change ((pullbackSpecIso R T B).inv ≫ (pullbackSymmetry _ _).hom) ≫
      pullback.snd _ _ = _
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact pullbackSpecIso_inv_fst' R T B)

/-- A finite etale algebra of constant rank acquires a concrete constant
scheme presentation over a constructed finite etale surjective cover. -/
theorem exists_affine_splitting_cover [Algebra.Etale R B] [Module.Finite R B]
    {n : ℕ} (hn : Module.rankAtStalk (R := R) B = n) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra R T),
      let u := Spec.map (CommRingCat.ofHom (algebraMap R T))
      IsFinite u ∧ Etale u ∧ Surjective u ∧
      ∃ r : ℕ, Nonempty
        (HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of T)) (Fin r) ≅ (Over.pullback u).obj (affineOver R B)) := by
  obtain ⟨T, _, _, hflat, hfinite, hetale, hsplit⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hn
  let u := Spec.map (CommRingCat.ofHom (algebraMap R T))
  have huFinite : IsFinite u :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfinite)
  have huEtale : Etale u :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr hetale)
  have huSurj : Surjective u := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  obtain ⟨r, ⟨e⟩⟩ := hsplit.nonempty_algEquiv_fun
  exact ⟨T, inferInstance, inferInstance, huFinite, huEtale, huSurj, r,
    ⟨constantAffineIso T r ≪≫ affineAlgIso T (T ⊗[R] B) e ≪≫ affineBaseChangeIso R B T⟩⟩

/-- No constant-rank hypothesis is needed locally: first restrict to a
principal open on which rank is constant, then construct the splitting
extension. The resulting etale neighborhood contains the specified point. -/
theorem exists_etale_splitting_at [Algebra.Etale R B] [Module.Finite R B]
    (p : PrimeSpectrum R) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra.Etale R T),
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R T)) ∧
      Algebra.IsFiniteSplit T (T ⊗[R] B) := by
  have : Module.FinitePresentation R B :=
    Module.FinitePresentation.of_finite_of_finitePresentation R B
  have hlc := Module.isLocallyConstant_rankAtStalk (R := R) (M := B)
  obtain ⟨_, ⟨a, rfl⟩, hp, ha⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp
    (hlc.isOpen_fiber (Module.rankAtStalk B p)) p rfl
  let R' := Localization.Away a
  have hrank : Module.rankAtStalk (R := R') (R' ⊗[R] B) = Module.rankAtStalk B p := by
    funext q
    rw [Module.rankAtStalk_baseChange]
    apply ha
    change PrimeSpectrum.comap (algebraMap R R') q ∈ (PrimeSpectrum.basicOpen a : Set _)
    rw [← PrimeSpectrum.localization_away_comap_range R' a]
    exact Set.mem_range_self q
  obtain ⟨T, _, _, _, _, _, hsplit⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hrank
  let : Algebra R T := ((algebraMap R' T).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' T := IsScalarTower.of_algebraMap_eq' rfl
  have he : Algebra.Etale R T := Algebra.Etale.comp R R' T
  have hsplit' : Algebra.IsFiniteSplit T (T ⊗[R] B) :=
    Algebra.IsFiniteSplit.of_algEquiv (Algebra.TensorProduct.cancelBaseChange R R' T T B)
  obtain ⟨q, hq⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R R')) := by
    rw [PrimeSpectrum.localization_away_comap_range R' a]
    exact hp
  obtain ⟨t, ht⟩ :=
    (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R') (B := T)) q
  refine ⟨T, inferInstance, inferInstance, he, ⟨t, ?_⟩, hsplit'⟩
  change PrimeSpectrum.comap (algebraMap R R') (PrimeSpectrum.comap (algebraMap R' T) t) = p
  rw [ht, hq]

/-- Every point of an affine base has an actual etale neighborhood on
which the given finite etale scheme is a finite constant scheme. -/
theorem exists_affine_scheme_splitting_at [Algebra.Etale R B] [Module.Finite R B]
    (p : Spec (.of R)) :
    ∃ (T : Type) (_ : CommRing T) (u : Spec (.of T) ⟶ Spec (.of R)),
      Etale u ∧ p ∈ Set.range u ∧ ∃ r : ℕ, Nonempty
        (HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of T)) (Fin r) ≅ (Over.pullback u).obj (affineOver R B)) := by
  obtain ⟨T, _, _, he, hp, hs⟩ := exists_etale_splitting_at R B p
  obtain ⟨r, ⟨e⟩⟩ := hs.nonempty_algEquiv_fun
  refine ⟨T, inferInstance, Spec.map (CommRingCat.ofHom (algebraMap R T)), ?_, hp, r,
    ⟨constantAffineIso T r ≪≫ affineAlgIso T (T ⊗[R] B) e ≪≫ affineBaseChangeIso R B T⟩⟩
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr he)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting
