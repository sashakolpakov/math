import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DeterminantTransition
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Hom

/-! # Resolution Orientation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionOrientation

noncomputable section

/-! Canonical quotient augmentations make the determinant transition an
identity for the same Ext group, computed with any projective resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.GeneratorMatrix OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology
  Exterior.KoszulResolution DeterminantTransition

universe u
variable (R : Type u) [CommRing R]

section Comparison
variable {M : ModuleCat.{u} R} (P Q S : ProjectiveResolution M)

def comparison (n : ℕ) :
    (DualComplexHomology.complex R P.complex).homology n ≅
      (DualComplexHomology.complex R Q.complex).homology n :=
  IntegralComparison.ProjectiveResolution.Hom.Comparison.homologyIso (ExactModuleDualFunctor.functor R) P Q n

theorem comparison_hom (n : ℕ) : (comparison R P Q n).hom =
    homologyMap (DualComplexHomology.map R (ProjectiveResolution.lift (𝟙 M) Q P)) n := rfl

theorem dual_map_comp {K L N : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : K ⟶ L) (g : L ⟶ N) : DualComplexHomology.map R (f ≫ g) =
      DualComplexHomology.map R g ≫ DualComplexHomology.map R f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro x
  rfl

theorem comparison_naturality (a : S.complex ⟶ Q.complex) (ha : a ≫ Q.π = S.π) (n : ℕ) :
    (comparison R P Q n).hom ≫ homologyMap (DualComplexHomology.map R a) n =
      (comparison R P S n).hom := by
  rw [comparison_hom, comparison_hom, ← homologyMap_comp, ← dual_map_comp]
  have h : Homotopy (a ≫ ProjectiveResolution.lift (𝟙 M) Q P)
      (ProjectiveResolution.lift (𝟙 M) S P) :=
    ProjectiveResolution.liftHomotopy (𝟙 M) _ _ (by simp [Category.assoc, ha]) (by simp)
  exact ((ExactModuleDualFunctor.functor R).mapHomotopy h.op).homologyMap_eq n

end Comparison

variable {n : ℕ} (I : Ideal R) (s : Fin n → R) (hs : OrientedTopCohomology.ideal R s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))

def resolutionAtIdeal : ProjectiveResolution (ModuleCat.of R (R ⧸ I)) where
  complex := OrientedTopCohomology.koszul R s
  projective m := inferInstance
  π := (Exterior.KoszulResolution.resolution R s hreg).π ≫ (ChainComplex.single₀ (ModuleCat R)).map
    (Submodule.quotEquivOfEq _ _ hs).toModuleIso.hom
  quasiIso := by
    have := (Exterior.KoszulResolution.resolution R s hreg).quasiIso
    exact quasiIso_comp _ _

@[simp] theorem resolutionAtIdeal_π_zero : (resolutionAtIdeal R I s hs hreg).π.f 0 =
    ModuleCat.ofHom (I.mkQ.comp (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap) := by
  simp only [resolutionAtIdeal, HomologicalComplex.comp_f, Exterior.KoszulResolution.resolution_π_f_zero,
    ChainComplex.single₀_map_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

variable (t : Fin n → R) (ht : OrientedTopCohomology.ideal R t = I)
  (htreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn t))
  (A : Matrix (Fin n) (Fin n) R) (hA : ∀ i, s i = ∑ j, A i j * t j)

theorem change_augmentation :
    GeneratorMatrix.change R s t A hA ≫ (resolutionAtIdeal R I t ht htreg).π =
      (resolutionAtIdeal R I s hs hreg).π := by
  apply HomologicalComplex.Hom.ext
  funext m
  cases m with
  | zero =>
      rw [HomologicalComplex.comp_f, resolutionAtIdeal_π_zero, resolutionAtIdeal_π_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change I.mkQ (exteriorPower.zeroEquiv R _
        (exteriorPower.map 0 (Matrix.toLin' A.transpose) x)) =
          I.mkQ (exteriorPower.zeroEquiv R _ x)
      exact congrArg I.mkQ (LinearMap.congr_fun
        (exteriorPower.zeroEquiv_naturality (Matrix.toLin' A.transpose)) x)
  | succ m =>
      exact (isZero_single_obj_X (.down ℕ) 0 (ModuleCat.of R (R ⧸ I)) (m + 1) (by omega)).eq_of_tgt _ _

variable (P : ProjectiveResolution (ModuleCat.of R (R ⧸ I)))

def purityIso : (DualComplexHomology.complex R P.complex).homology n ≅
    ModuleCat.of R (R ⧸ I) :=
  comparison R P (resolutionAtIdeal R I s hs hreg) n ≪≫ DeterminantTransition.isoToIdeal R I s hs

include hA in
theorem purity_transition : (purityIso R I s hs hreg P).hom =
    (purityIso R I t ht htreg P).hom ≫
      ModuleCat.ofHom (A.det • (LinearMap.id : (R ⧸ I) →ₗ[R] (R ⧸ I))) := by
  have h := comparison_naturality R P (resolutionAtIdeal R I t ht htreg)
    (resolutionAtIdeal R I s hs hreg) (GeneratorMatrix.change R s t A hA)
    (change_augmentation R I s hs hreg t ht htreg A hA) n
  dsimp only [purityIso, Iso.trans_hom]
  rw [← h, Category.assoc]
  change _ ≫ (homologyMap (DeterminantTransition.dualChange R s t A hA) n ≫ (DeterminantTransition.isoToIdeal R I s hs).hom) = _
  rw [DeterminantTransition.homology_transition R I s t hs ht A hA, ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionOrientation
